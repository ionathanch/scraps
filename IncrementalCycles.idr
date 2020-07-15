import Data.SortedMap

-- lookup returns a Maybe, but we won't ever access a nonexistent vertex
-- so we set the totality checker to partial by default... for now
-- Is there a "noncovering" flag to use instead?
%default partial

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

record Graph a where
  constructor mkGraph
  nextMark : Mark
  graph : SortedMap a (Vertex a)

(Eq a) => Eq (Vertex a) where
  v1 == v2 = v1.name == v2.name


Get : {a: Type} -> Type -> Type
Get b = Graph a -> a -> b

Set : {a: Type} -> Type -> Type
Set b = Graph a -> a -> b -> Graph a

Update : {a: Type} -> Type
Update = Graph a -> a -> Graph a

getter : (Vertex a -> b) -> Get {a = a} b
getter get g k =
  let Just v = lookup k g.graph
  in get v

setter : (Vertex a -> Vertex a) -> Update {a = a}
setter set g k =
  let Just v = lookup k g.graph
  in record { graph $= insert k (set v) } g


newMark : Graph a -> (Graph a, Mark)
newMark g = (record { nextMark $= (+ 1) } g, g.nextMark)

isMarked : Mark -> Get Bool
isMarked m g k = (m == ) $ getter mark g k

setMark : Set Mark
setMark g k m = setter (record { mark = m }) g k

getLevel : Get Int
getLevel = getter level

setLevel : Set Int
setLevel g k l = setter (record { level = l }) g k

getIncoming : Get {a = a} (List a)
getIncoming = getter incoming

clearIncoming : Update
clearIncoming g k = setter (record { incoming = [] }) g k

addIncoming : Set {a = a} a
addIncoming g k1 k2 = setter (record { incoming $= (k2 ::) }) g k1

getOutgoing : Get {a = a} (List a)
getOutgoing = getter outgoing

setParent : Set {a = a} a
setParent g k p = setter (record { parent = p }) g k

addEdge : Set {a = a} a
addEdge g k1 k2 = setter (record { outgoing $= (k2 ::) }) g k1


initGraph : Ord a => Graph a
initGraph = mkGraph 0 empty

newVertex : a -> Graph a -> Graph a
newVertex k g =
  let v = mkVertex k [] [] (-1) 1 k
  in record { graph $= insert k v } g


-- CYCLE DETECTION

data InterruptibleFoldStep a b = Continue a | Break b

-- What a long-ass name
ILFS : Type -> Type -> Type
ILFS a b = InterruptibleFoldStep a b

interruptibleFold : (a -> b -> ILFS b c) -> List a -> b -> ILFS b c
interruptibleFold _ [] acc = Continue acc
interruptibleFold f (x :: xs) acc = resume (f x acc)
  where
    resume : ILFS b c -> ILFS b c
    resume (Continue acc) = interruptibleFold f xs acc
    resume res@(Break _) = res


data VisitBackwardResult =
    VisitBackwardCompleted
  | VisitBackwardInterrupted
  | VisitBackwardCyclic

visitBackward : Ord a => Graph a -> a -> Mark -> Int -> List a -> (Graph a, VisitBackwardResult)
visitBackward g _ _ _ [] = (g, VisitBackwardCompleted)
visitBackward g target mark fuel (vertex :: stack) =
  let res = interruptibleFold folder (getIncoming g vertex) (g, stack, fuel)
  in case res of
    Break (g, True) => (g, VisitBackwardInterrupted)
    Break (g, False) => (setParent g target vertex, VisitBackwardCyclic)
    Continue (g, stack, fuel) => visitBackward g target mark fuel stack
  where
    Acc : Type -> Type
    Acc a = (Graph a, List a, Int)

    folder : a -> Acc a -> ILFS (Acc a) (Graph a, Bool)
    folder y (g, stack, fuel) =
      if fuel == 0 then Break (g, True) else
      if isMarked mark g y then Continue (g, stack, fuel - 1) else
      if y == target then Break (g, False) else
      let g = setMark g y mark
          g = setParent g y vertex
      in Continue (g, y :: stack, fuel - 1)

data BackwardSearchResult =
    BackwardForward Int Mark
  | BackwardCyclic
  | BackwardAcyclic

backwardSearch : Ord a => Int -> Graph a -> a -> a -> (Graph a, BackwardSearchResult)
backwardSearch fuel g v w =
  let (g, mark) = newMark g
      level = getLevel g v
      g = setMark g v mark
  in visit mark level (visitBackward g w mark fuel [v])
  where
    visit : Mark -> Int -> (Graph a, VisitBackwardResult) -> (Graph a, BackwardSearchResult)
    visit _ _ (g, VisitBackwardCyclic) = (g, BackwardCyclic)
    visit mark vLevel (g, VisitBackwardInterrupted) = (g, BackwardForward (vLevel + 1) mark)
    visit mark vLevel (g, VisitBackwardCompleted) =
      let wLevel = getLevel g w
      in (g,
        if vLevel == wLevel
        then BackwardAcyclic
        else BackwardForward vLevel mark)


data ForwardSearchResult a =
    ForwardCyclic a a
  | ForwardCompleted

visitForward : Ord a => Graph a -> Int -> Mark -> List a -> (Graph a, ForwardSearchResult a)
visitForward g _ _ [] = (g, ForwardCompleted)
visitForward g newLevel visited (x :: stack) =
  let res = interruptibleFold folder (getOutgoing g x) (g, stack)
  in case res of
    Break (g, y) => (g, ForwardCyclic x y)
    Continue (g, stack) => visitForward g newLevel visited stack
  where
    Acc : Type -> Type
    Acc a = (Graph a, List a)

    folder : a -> Acc a -> ILFS (Acc a) (Graph a, a)
    folder y (g, stack) =
      if isMarked visited g y then Break (g, y) else
      let yLevel = getLevel g y
          g = setParent g y x
      in if yLevel < newLevel then
        let g = setLevel g y newLevel
            g = clearIncoming g y
            g = addIncoming g y x
        in Continue (g, y :: stack)
      else if yLevel == newLevel then
        let g = addIncoming g y x
        in Continue (g, stack)
      else Continue (g, stack)

forwardSearch : Ord a => Graph a -> a -> Int -> Mark -> (Graph a, ForwardSearchResult a)
forwardSearch g w newLevel visited =
  let g = clearIncoming g w
      g = setLevel g w newLevel
  in visitForward g newLevel visited [w]


data AddEdgeResult a = EdgeAdded | EdgeCreatesCycle -- (() -> List a)

addEdgeOrDetectCycle : Ord a => Graph a -> a -> a -> (Graph a, AddEdgeResult a)
addEdgeOrDetectCycle g v w =
  if v == w then (g, EdgeCreatesCycle) else
  if getLevel g v < getLevel g w then succeed g else
  case backwardSearch (getLevel g v) g v w of
    (g, BackwardAcyclic) => succeed g
    (g, BackwardCyclic) => (g, EdgeCreatesCycle)
    (g, BackwardForward newLevel visited) =>
      case forwardSearch g w newLevel visited of
        (g, ForwardCompleted) => succeed g
        (g, ForwardCyclic z t) => (g, EdgeCreatesCycle)
  where
    succeed : Graph a -> (Graph a, AddEdgeResult a)
    succeed g =
      let g = addEdge g v w
      in if getLevel g v == getLevel g w
        then (addIncoming g w v, EdgeAdded)
        else (g, EdgeAdded)
