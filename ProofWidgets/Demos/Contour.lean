import ProofWidgets.Demos.ContourInteractive

import Lean.Expr
import Lean.Elab.Tactic

import Lean.Data.Json.FromToJson
import Lean.Parser
import Lean.PrettyPrinter.Delaborator.Basic
import Lean.Server.Rpc.Basic

import ProofWidgets.Component.Basic


open Lean Expr

def constName? : Expr → Option Name
  | const n _ => some n
  | _         => none

/-- If the expression is a constant, return that name. Otherwise return `Name.anonymous`. -/
def Lean.Expr.constName (e : Expr) : Name :=
  e.constName?.getD Name.anonymous

/-- Return the function (name) and arguments of an application. -/
def Lean.Expr.getAppFnArgs (e : Expr) : Name × Array Expr :=
  Lean.Expr.withApp e λ e a => (e.constName, a)

/--
  Return `some n` if `e` is one of the following
  - A nat literal (numeral)
  - `Nat.zero`
  - `Nat.succ x` where `isNumeral x`
  - `OfNat.ofNat _ x _` where `isNumeral x` -/
partial def Lean.Expr.numeral? (e : Expr) : Option Nat :=
  if let some n := e.natLit? then n
  else
    let f := e.getAppFn
    if !f.isConst then none
    else
      let fName := f.constName!
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then (numeral? e.appArg!).map Nat.succ
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then numeral? (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then some 0
      else none


universe u

def Line (a b : Nat × Nat) : Nat → Nat × Nat := fun t => ((1 - t) * a.1 + b.1, (1 - t) * a.2 + b.2)

partial def isLine (e : Expr) : Option ((Nat × Nat) × (Nat × Nat)) :=
  match e.getAppFnArgs with
  | (``Line, #[e1, e2]) =>
    match e1.getAppFnArgs, e2.getAppFnArgs with
    | (``Prod.mk, #[_, _, a, b]), (``Prod.mk, #[_, _, c, d]) =>
      match a.numeral?, b.numeral?, c.numeral?, d.numeral? with
      | some a', some b', some c', some d' =>
        some ((a', b'), c', d')
      | _, _, _, _ => none
    | _, _ => none
  | _ => none

open scoped ProofWidgets.Jsx
#html <Contour nodes = {#[⟨20, 20⟩, ⟨4.5, 6.0⟩]} edges = {#[⟨⟨10, 10⟩, ⟨500, 10⟩⟩]} arcs = {#[⟨⟨500, 10⟩, 10, 0, 3.14 * 2⟩, ⟨⟨500 - 20, 10⟩, 20, 0, 3.14⟩]} />


open Elab Tactic Json

-- REFERENCE:
-- @[widget_module]
-- def HtmlDisplayPanel : Component HtmlDisplayProps where
--   javascript := include_str ".." / ".." / "build" / "js" / "htmlDisplayPanel.js"
--
-- @[tactic htmlTac]
-- def elabHtmlTac : Tactic
--   | stx@`(tactic| html! $t:term) => do
--     let ht ← evalHtml <| ← `(ProofWidgets.Html.ofTHtml $t)
--     savePanelWidgetInfo stx ``HtmlDisplayPanel do
--       return json% { html: $(← rpcEncode ht) }
--   | stx => throwError "Unexpected syntax {stx}."

syntax (name := wowTacStx) "wow " : tactic

-- TODO :: add ability for the lines to be auto labeled based on the their user names
@[tactic wowTacStx]
def wow : Tactic
  | stx@`(tactic| wow) => withMainContext do
    let mut vertices : List (Nat × Nat) := []
    let mut exprList : List (Option Expr) := []

    let mut edges : List line := []

    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    for decl in ctx do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- **NEW:** Find the type.
      exprList := decl.value? :: exprList
      match decl.value? with
      | some val =>
        match isLine val with
        | some ((a, b), (c, d)) =>
          vertices := ((a, b) :: vertices)
          vertices := ((c, d) :: vertices)

          edges := ⟨⟨a.toFloat, b.toFloat⟩, ⟨c.toFloat, d.toFloat⟩⟩ :: edges
        | none => pure ()
      | none => pure ()
    dbg_trace f!"{vertices} {exprList}"
    ProofWidgets.savePanelWidgetInfo stx ``Contour do
      return ToJson.toJson ({width := 120, height := 70, margin := 10, nodes := #[], edges := edges.toArray, arcs := #[]} : ContourProps)
  | _ => throwUnsupportedSyntax

example {α : Type} : 2 + 2 = 5 := by
  let bruh := Line (0, 0) (100, 0)
  let bruh2 := Line (100, 0) (100, 100)
  let bruh3 := Line (100, 100) (0, 100)
  let bruh4 := Line (0, 100) (0, 0)
  let wow := 2 + 2 = 4
  wow
