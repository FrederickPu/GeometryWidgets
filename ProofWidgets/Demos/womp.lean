import Lean.Elab.Tactic
import Lean.Meta.ExprLens
import Lean.Meta

import ProofWidgets.Component.HtmlDisplay

import ProofWidgets.Component.Basic
import ProofWidgets.Presentation.Expr -- Needed for RPC calls in PresentSelectionPanel

import Lean.Server.Rpc.Basic
import ProofWidgets.Data.Html

set_option pp.rawOnError true

namespace ProofWidgets
open Lean Server

syntax (name := wowTacStx) "wow " : tactic

open Elab Tactic Json  in

partial def isEq (red : TransparencyMode) (e : Expr) : Bool :=
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, e1, e2]) => do
    let (m1, comp1) ← linearFormOfExpr red m e1
    let (m2, comp2) ← linearFormOfExpr red m1 e2
    return (m2, comp1.mul comp2)

@[tactic wowTacStx]
def wow : Tactic
  | stx@`(tactic| wow) =>
    Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- **NEW:** Find the type.
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr} | type: {declType}"
  | _ => throwUnsupportedSyntax

#check Expr.dbgToString
#check Lean.Meta.getLocalHyps
end ProofWidgets


example (a b : Nat) : 1 = 0 ∨ True →  2 + 2 = 4 → 0 = 0 := by
  intro w
  !html
  cases w with
  | inl l => {
    intro h
    have : 1 + 1 = 2 ∧ 2 =2 := ⟨by rfl, by rfl⟩
    have := this.left
    wow
   }
  html! <span>alsijdalskj</span>
  intro h
  wow
