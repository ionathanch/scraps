{-
  An implementation of incremental cycle detection in a directed graph.
  This is based directly on this OCaml implementation: https://gitlab.inria.fr/agueneau/incremental-cycles
  which is accompanied by a formal proof of time complexity: https://doi.org/10.4230/LIPIcs.ITP.2019.18
  This is in turn based on a very similar algorithm: https://doi.org/10.1145/2756553
  which is cited in Coq's implementation: https://github.com/coq/coq/blob/master/lib/acyclicGraph.ml
-}

import Data.SortedMap
import Data.List
import Control.Monad.State

-- lookup returns a Maybe, but we won't ever access a nonexistent vertex
-- so we set the totality checker to partial by default... for now
-- Is there a "noncovering" flag to use instead?
%default partial

-- Why isn't this in Prelude.Interfaces??
(>>) : Monad m => m a -> m b -> m b
a >> b = a >>= \_ => b

-- RAW GRAPH

Mark : Type
Mark = Int

record Vertex a where
  constructor mkVertex
  name : a
  outgoing : List a
  incoming : List a
  mark : Mark
  level : Int
  parent : a

public export
record Graph a where
  constructor mkGraph
  nextMark : Mark
  graph : SortedMap a (Vertex a)

GState : Type -> Type -> Type
GState a = State (Graph a)

getter : a -> (Vertex a -> b) -> GState a b
getter k get = do
  Just v <- gets $ lookup k . graph
  pure $ get v

setter : a -> (Vertex a -> Vertex a) -> GState a ()
setter k set = do
  Just v <- gets $ lookup k . graph
  modify $ record { graph $= insert k (set v) }


newMark : GState a Mark
newMark = do
  mark <- gets nextMark
  modify $ record { nextMark $= (+ 1) }
  pure mark

isMarked : a -> Mark -> GState a Bool
isMarked k m = (m == ) <$> getter k mark

setMark : a -> Mark -> GState a ()
setMark k m = setter k (record { mark = m })

getLevel : a -> GState a Int
getLevel k = getter k level

setLevel : a -> Int -> GState a ()
setLevel k l = setter k (record { level = l })

getIncoming : a -> GState a (List a)
getIncoming k = getter k incoming

clearIncoming : a -> GState a ()
clearIncoming k = setter k (record { incoming = [] })

addIncoming : a -> a -> GState a ()
addIncoming k1 k2 = setter k1 (record { incoming $= (k2 ::) })

getOutgoing : a -> GState a (List a)
getOutgoing k = getter k outgoing

setParent : a -> a -> GState a ()
setParent k p = setter k (record { parent = p })

getParent : a -> GState a a
getParent k = getter k parent

insertEdge : a -> a -> GState a ()
insertEdge k1 k2 = setter k1 (record { outgoing $= (k2 ::) })


export
initGraph : Ord a => Graph a
initGraph = mkGraph 0 empty

export
newVertex : Ord a => a -> Graph a -> Graph a
newVertex k =
  let v = mkVertex k [] [] (-1) 1 k
  in record { graph $= insert k v }


-- CYCLE DETECTION

data InterruptibleFoldStep a b = Continue a | Break b

-- What a long-ass name
ILFS : Type -> Type -> Type
ILFS a b = InterruptibleFoldStep a b

interruptibleFold : (a -> b -> GState a (ILFS b c)) -> List a -> b -> GState a (ILFS b c)
interruptibleFold _ [] acc = pure $ Continue acc
interruptibleFold f (x :: xs) acc = do
  res <- (f x acc)
  case res of
    Continue acc => interruptibleFold f xs acc
    Break _ => pure $ res

{-
  An interlude on formatting:
  Throughout the below I've scattered a number of redundant `do`s, usually in if-then-else expressions, e.g.
    if ... then do
      ... else do
    if ... then do
      ... else do
    ...
  This is to trick the parser into letting me deindent the body of the else branch.
  Otherwise, the code would start leaning to one side like this:
    if ... then do
      ...
      else if ... then do
        ...
        else ...
  This is to imitate how if-then-else expressions usually appear outside of `do`s:
    if ... then
      ...
    else if ... then
      ...
    else ...
  Unfortunately, this isn't possible since inside a `do` block,
  the parser thinks each `else` line is a new monadic statement.
-}

data VisitBackwardResult =
    VisitBackwardCompleted
  | VisitBackwardInterrupted
  | VisitBackwardCyclic

visitBackward : Eq a => a -> Mark -> Int -> List a -> GState a VisitBackwardResult
visitBackward _ _ _ [] = pure VisitBackwardCompleted
visitBackward target mark fuel (vertex :: stack) = do
  incoming <- getIncoming vertex
  res <- interruptibleFold folder incoming (stack, fuel)
  case res of
    Break True => pure VisitBackwardInterrupted
    Break False => setParent target vertex >> pure VisitBackwardCyclic
    Continue (stack, fuel) => visitBackward target mark fuel stack
  where
    folder : a -> (List a, Int) -> GState a (ILFS (List a, Int) Bool)
    folder y (stack, fuel) =
      if fuel == 0 then
        pure $ Break True else do
      marked <- isMarked y mark
      if marked then
        pure $ Continue (stack, fuel - 1) else do
      if y == target then
        pure $ Break False else do
      setMark y mark
      setParent y vertex
      pure $ Continue (y :: stack, fuel - 1)

data BackwardSearchResult =
    BackwardForward Int Mark
  | BackwardCyclic
  | BackwardAcyclic

backwardSearch : Eq a => Int -> a -> a -> GState a BackwardSearchResult
backwardSearch fuel v w = do
  mark <- newMark
  vlevel <- getLevel v
  setMark v mark
  res <- visitBackward w mark fuel [v]
  case res of
    VisitBackwardCyclic => pure $ BackwardCyclic
    VisitBackwardInterrupted => pure $ BackwardForward (vlevel + 1) mark
    VisitBackwardCompleted => do
      wlevel <- getLevel w
      if vlevel == wlevel then
        pure BackwardAcyclic else do
      pure $ BackwardForward vlevel mark


data ForwardSearchResult a =
    ForwardCyclic a a
  | ForwardCompleted

visitForward : Int -> Mark -> List a -> GState a (ForwardSearchResult a)
visitForward _ _ [] = pure $ ForwardCompleted
visitForward newlevel visited (x :: stack) = do
  outgoing <- getOutgoing x
  res <- interruptibleFold folder outgoing stack
  case res of
    Break y => pure $ ForwardCyclic x y
    Continue stack => visitForward newlevel visited stack
  where
    folder : a -> List a -> GState a (ILFS (List a) a)
    folder y stack = do
      marked <- isMarked y visited
      if marked then
        pure $ Break y else do
      ylevel <- getLevel y
      setParent y x
      if ylevel < newlevel then do
        setLevel y newlevel
        clearIncoming y
        addIncoming y x
        pure $ Continue (y :: stack) else do
      if ylevel == newlevel then do
        addIncoming y x
        pure $ Continue stack else do
      pure $ Continue stack

forwardSearch : a -> Int -> Mark -> GState a (ForwardSearchResult a)
forwardSearch w newlevel visited = do
  clearIncoming w
  setLevel w newlevel
  visitForward newlevel visited [w]


public export
data AddEdgeResult a = EdgeAdded | EdgeCreatesCycle (List a)

listOfParents : Eq a => a -> a -> List a -> GState a (List a)
listOfParents x y acc =
  if x == y then pure $ acc else do
  p <- getParent x
  let acc' = p :: acc
  if p == y then pure $ acc else do
  listOfParents p y acc'

computeCycle : Eq a => a -> a -> a -> a -> GState a (List a)
computeCycle v w z t = do
  parents <- listOfParents t v []
  listOfParents z w (z :: t :: reverse parents)

addEdgeOrDetectCycle : Eq a => a -> a -> GState a (AddEdgeResult a)
addEdgeOrDetectCycle v w =
  if v == w then
    pure $ EdgeCreatesCycle [v] else do
  vlevel <- getLevel v
  wlevel <- getLevel w
  if vlevel < wlevel then
    succeed () else do
  level <- getLevel v
  res <- backwardSearch level v w
  case res of
    BackwardCyclic => do
      cycle <- listOfParents w v []
      pure $ EdgeCreatesCycle cycle
    BackwardAcyclic => succeed ()
    BackwardForward newlevel visited => do
      res <- forwardSearch w newlevel visited
      case res of
        ForwardCyclic z t => do
          cycle <- computeCycle v w z t
          pure $ EdgeCreatesCycle cycle
        ForwardCompleted => succeed ()
  where
    succeed : () -> GState a (AddEdgeResult a)
    succeed () = do
      insertEdge v w
      vlevel <- getLevel v
      wlevel <- getLevel w
      if vlevel == wlevel then do
        addIncoming w v
        pure $ EdgeAdded else do
      pure $ EdgeAdded

export
addEdge : Eq a => a -> a -> Graph a -> (AddEdgeResult a, Graph a)
addEdge v w g =
  runState (addEdgeOrDetectCycle v w) g