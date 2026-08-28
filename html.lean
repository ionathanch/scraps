module

public meta import Lean

set_option autoImplicit false
set_option pp.proofs true

public structure Attribute where
  name : String
  value : String

public inductive HTML where
  | str : String → HTML
  | mk : String → List Attribute → List HTML → HTML
  | mkClos : String → List Attribute → HTML

declare_syntax_cat attrib
declare_syntax_cat html

-- `class` is a Lean keyword and also an HTML attribute name,
-- so we use `rawIdent` to ignore reserved keywords
syntax (name := attrib) rawIdent " = " str : attrib
syntax (name := attribBool) rawIdent : attrib

-- `section` and `meta` are Lean keywords and also HTML elements,
-- so we use `rawIdent` to ignore reserved keywords
syntax (name := html) "<" rawIdent attrib* ">" html* "</" rawIdent ">" : html
syntax (name := htmlClos) "<" rawIdent attrib* "/>" : html
syntax (name := htmlText) str : html

meta section
open Lean Elab Meta Term

def Lean.HTMLTypeLit : Expr := (.const ``HTML [])
def Lean.attributeTypeLit : Expr := (.const ``_root_.Attribute [])

@[term_elab attrib]
public def elabAttribute : TermElab := λ stx _ ↦ do
  match stx with
  | `(attrib| $name:ident = $value:str) =>
    mkAppM ``Attribute.mk #[
      mkStrLit name.getId.toString,
      mkStrLit value.getString]
  | `(attrib| $name:ident) =>
    mkAppM ``Attribute.mk #[
      mkStrLit name.getId.toString,
      mkStrLit ""]
  | _ => throwError m!"cannot parse {stx} as attribute"

@[term_elab html, term_elab htmlClos, term_elab htmlText]
public def elabHTML : TermElab := λ stx _type? ↦ do
  match stx with
  | `(html| < $tagOpen:ident $[$attribs:attrib]* > $[$ts:html]* </ $tagClose:ident >) =>
    unless tagOpen.getId == tagClose.getId do
      withRef tagClose do
        throwError m!"closing tag {tagClose} does not match opening tag {tagOpen}"
    let children ← ts.toList.mapM (elabTerm ·.raw (some HTMLTypeLit))
    mkAppM ``HTML.mk #[
      mkStrLit tagOpen.getId.toString,
      ← mkListLit attributeTypeLit
        (← attribs.toList.mapM (elabAttribute ·.raw none)),
      ← mkListLit HTMLTypeLit children]
  | `(htmlClos| < $tag:ident $[$attribs:attrib]* />) =>
    mkAppM ``HTML.mkClos #[
      mkStrLit tag.getId.toString,
      ← mkListLit attributeTypeLit
        (← attribs.toList.mapM (elabAttribute ·.raw none))]
  | `(htmlText| $s:str) =>
    mkAppM ``HTML.str #[mkStrLit s.getString]
  | _ => throwError m!"cannot elaborate {stx} as HTML"

elab "<" ("!doctype" <|> "!DOCTYPE") "html" ">" stxs:html* : term => do
  mkListLit HTMLTypeLit
    (← stxs.toList.mapM (elabHTML ·.raw (some HTMLTypeLit)))

end -- meta section

def test : List HTML :=
  <!doctype html>
  <html lang="en-CA">
    <head>
      <meta name="author" content="ionchy" />
      <title>r#"HTML in Lean"#</title>
    </head>
    <body>
      <main>
        <h1>r#"Elaborating HTML tags as Lean HTML terms"#</h1>
        <article>
          <section></section>
        </article>
      </main>
    </body>
  </html>

/-- info: private def test : List HTML :=
[HTML.mk "html" [{ name := "lang", value := "en-CA" }]
    [HTML.mk "head" []
        [HTML.mkClos "meta" [{ name := "name", value := "author" }, { name := "content", value := "ionchy" }],
          HTML.mk "title" [] [HTML.str "HTML in Lean"]],
      HTML.mk "body" []
        [HTML.mk "main" []
            [HTML.mk "h1" [] [HTML.str "Elaborating HTML tags as Lean HTML terms"],
              HTML.mk "article" [] [HTML.mk "section" [] []]]]]] -/
#guard_msgs in
#print test
