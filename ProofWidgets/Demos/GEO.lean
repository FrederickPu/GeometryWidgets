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



/-- Uniform at random in [0, 1)-/
def randomFloat {gen} [RandomGen gen] (g : gen) : Float × gen :=
  let (n, g') := RandomGen.next g
  let (lo, hi) := RandomGen.range g
  (Float.ofNat (n - lo) / Float.ofNat (hi - lo + 1), g')

def IO.randFloat (lo := 0.0) (hi := 1.0) : IO Float := do
  let gen ← IO.stdGenRef.get
  let (r, gen) := randomFloat gen
  IO.stdGenRef.set gen
  return lo + (hi - lo) * r

def IO.randPoint (lo := 0.0) (hi := 1.0) : IO (Float × Float) := do
  return ⟨← IO.randFloat lo hi, ← IO.randFloat lo hi⟩


universe u
class Bet (α : Type u) where
  (bet : α → α → α → Prop)

partial def isBet (e : Expr) : Option (Expr × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Bet.bet, #[_, _, e1, e2, e3]) => (e1, e2, e3) -- eg ::  [Int, inst, 1, 2, 3]
  | _ => none

structure BetSeq
  (exprMap : ExprMap Nat)
  (betOps : List (Nat × Nat × Nat))

instance : HAdd (Float × Float) (Float × Float) (Float × Float) := {
  hAdd := fun ⟨a, b⟩ => fun ⟨d, e⟩ => (a + d, b + e)
}
instance : HSub (Float × Float) (Float × Float) (Float × Float) := {
  hSub := fun ⟨a, b⟩ => fun ⟨d, e⟩ => (a - d, b - e)
}
instance : HMul (Float × Float) Float (Float × Float) := {
  hMul := fun ⟨a, b⟩ => fun c => (a * c, b * c)
}

structure point where
  id : Nat
  x : Float
  y : Float
  deriving ToJson, FromJson
structure edge where
  startNodeId : Nat
  endNodeId : Nat
  deriving ToJson, FromJson
structure BanProps where
  nodes : Array point := #[]
  edges : Array edge := #[]
  deriving ToJson, FromJson, Inhabited
def toBanProps (exprMap : ExprMap Nat) (points : HashMap Nat (Float × Float)) (vertices : List (Nat × Nat)) : BanProps := Id.run do
  let wow1 : List point := exprMap.toList.map (fun ⟨e, n⟩ => ⟨n, (points.find! n).1, (points.find! n).2⟩)
  let wow2 : List edge := vertices.map (fun ⟨id1, id2⟩ => ⟨id1, id2⟩)
  return ⟨wow1.toArray, wow2.toArray⟩
@[widget_module]
def BanDisplayPanel : ProofWidgets.Component BanProps where
  javascript := include_str ".." / ".." / "build" / "js" / "banana.js"
@[widget_module]
def BanPanel : ProofWidgets.Component BanProps where
  javascript := include_str ".." / ".." / "build" / "js" / "bananaPanel.js"

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

@[tactic wowTacStx]
def wow : Tactic
  | stx@`(tactic| wow) => withMainContext do
    let mut out : List (Nat × Nat × Nat) := []
    let mut exprMap : ExprMap Nat := ∅
    let mut points : HashMap Nat (Float × Float) := ∅
    let mut vertices : List (Nat × Nat) := []
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    for decl in ctx do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- **NEW:** Find the type.
      match isBet declType with
      | some (a, b, c) =>
        if !exprMap.contains a then
          exprMap := exprMap.insert a exprMap.size
        if !exprMap.contains b then
          exprMap := exprMap.insert b exprMap.size
        if !exprMap.contains c then
          exprMap := exprMap.insert c exprMap.size
        let a' := exprMap.find! a
        let b' := exprMap.find! b
        let c' := exprMap.find! c
        if ! (vertices.contains (a', b') ∨ vertices.contains (b', a')) then
            vertices := vertices.cons (a', b')
        if ! (vertices.contains (b', c') ∨ vertices.contains (c', b')) then
          vertices := vertices.cons (b', c')

        let p1 ← IO.randPoint 0 25
        let p2 ← IO.randPoint 0 25
        match points.contains a', points.contains b', points.contains c' with
        | false, true, true =>
          points := points.insert a' ((points.find! b') - (points.find! c') + points.find! b')
        | true, false, true =>
          points := points.insert b' ((points.find! a' + points.find! c')*0.5)
        | true, true, false =>
          points := points.insert c' ((points.find! b') - (points.find! a') + points.find! b')
        | true, false, false =>
          points := points.insert b' (points.find! a' + p1)
          points := points.insert c' (points.find! a' + p1 + p1)
        | false, true, false =>
          points := points.insert a' (points.find! b' - p1)
          points := points.insert c' (points.find! b' + p1)
        | false, false, true =>
          points := points.insert b' (points.find! c' + p1)
          points := points.insert a' (points.find! c' + p1 + p1)
        | false, false, false =>
          points := (points.insert a' p1).insert b' (p1 + p2)
          points := points.insert c' (p1 + p2 + p2)
        | true, true, true => points := points
        out := List.cons (exprMap.find! a, exprMap.find! b, exprMap.find! c) out
      | none => pure ()
    ProofWidgets.savePanelWidgetInfo stx ``BanDisplayPanel do
        return ToJson.toJson (toBanProps exprMap points vertices)
    dbg_trace f!"{points.toList}"
      -- let declExpr := decl.toExpr -- Find the expression of the declaration.
      -- let declName := decl.userName -- Find the name of the declaration.
      -- let declType ← Lean.Meta.inferType declExpr -- **NEW:** Find the type.
      -- match isBet declType with
      -- | some x => dbg_trace f!"+ local decl: name: {declName} | isEq : {isEq declType} | isBet : {x}"
      -- | none => pure ()
  | _ => throwUnsupportedSyntax

example {α : Type} [Bet Int] : Bet.bet (1 : Int) 2 3 → Bet.bet (1 : Int) (1 + 1) 3 → Bet.bet (7 : Int) (1 + 1) 12 → 1 + 1 = 2 := by
  intro h h1 h3
  wow
