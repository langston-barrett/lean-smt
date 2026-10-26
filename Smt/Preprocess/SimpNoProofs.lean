/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Langston Barrett
-/

module

public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp

/-!
`simp` on a goal whose proof is discarded, as under `smt (trust := true)`.

The preprocessing steps revert the hypotheses and simplify the goal
`∀ x₁ … xₙ, h₁ → … → hₘ → False`. For each binder, `simp` builds a congruence proof
(`forall_congr`, `implies_congr`) that abstracts the proof for the binders under it, which
takes time quadratic in the number of binders. Here, `simp` handles `∀` and `→` as usual,
except that the proof of each is a placeholder (`sorryAx`) of the right type, of constant size.
The simplified expression is the same as `simp`'s.

This is only sound when the proof is never used, i.e., when the goal is admitted.
-/

public meta section

namespace Smt.Preprocess

open Lean Meta

namespace SimpNoProofs

/-- A placeholder proof of `lhs = rhs`. -/
def placeholder (lhs rhs : Expr) : MetaM Expr := do
  let u ← getLevel lhs
  return mkApp2 (.const ``sorryAx [.zero])
    (mkApp3 (.const ``Eq [.succ u]) (.sort u) lhs rhs) (.const ``Bool.false [])

/-- Replace `r`'s proof that `e = r.expr`, if any, by a placeholder. -/
def collapse (e : Expr) (r : Simp.Result) : MetaM Simp.Result := do
  match r.proof? with
  | none   => return r
  | some _ => return { r with proof? := some (← placeholder e r.expr) }

/-- Compose `r₁ : a = b` and `r₂ : b = c` like `Simp.Result.mkEqTrans`, except that the proof is
only kept to record that there is one: `collapse` replaces it. -/
def trans (r₁ r₂ : Simp.Result) : Simp.Result :=
  { r₂ with proof? := r₁.proof? <|> r₂.proof?, cache := r₁.cache && r₂.cache }

/-- `Simp.simpForall`, but with a placeholder proof. -/
def simpForall (e : Expr) : Simp.SimpM Simp.Result := Simp.withParent e do
  if e.isArrow then
    -- `Simp.simpArrow`. With `contextual`, it uses the proof of the domain.
    if (← Simp.getConfig).contextual then
      return ← Simp.simpForall e
    let rp ← Simp.simp e.bindingDomain!
    let rq ← Simp.simp e.bindingBody!
    let r := { expr := e.updateForallE! rp.expr rq.expr, proof? := rp.proof? <|> rq.proof? }
    collapse e r
  else if (← isProp e) then
    -- `simp` puts the proof that the domain was simplified in the body.
    if (← isProp e.bindingDomain!) then
      return ← Simp.simpForall e
    let domain ← Simp.dsimp e.bindingDomain!
    withLocalDecl e.bindingName! e.bindingInfo! domain fun x => Simp.withNewLemmas #[x] do
      let rb ← Simp.simp (e.bindingBody!.instantiate1 x)
      let eNew ← mkForallFVars #[x] rb.expr
      collapse e { expr := eNew, proof? := rb.proof? }
  else
    return { expr := (← Simp.dsimp e) }

/-- Wrap `simp`'s `pre` method so that it simplifies `∀` and `→` with placeholder proofs.
After `pre`, it does what `Simp.simpLoop` does for these (whose `reduceStep` leaves them
unchanged), then returns `.done` so that `simpLoop` does not. -/
def pre (pre : Simp.Simproc) : Simp.Simproc := fun e => do
  let step ← pre e
  let r ← match step with
    | .continue none     => pure { expr := e }
    | .continue (some r) => pure r
    | _                  => return step
  unless r.expr.isForall do
    return step
  let r := trans r (← simpForall r.expr)
  let r ← match (← Simp.post r.expr) with
    | .done r' => return .done (← collapse e (trans r r'))
    | .continue none => pure r
    | .visit r' | .continue (some r') => pure (trans r r')
  let r ←
    if (← Simp.getConfig).singlePass || e == r.expr then
      pure r
    else
      pure (trans r (← Simp.simp r.expr))
  return .done (← collapse e r)

end SimpNoProofs

/-- `Meta.simpTarget` without a discharger and with `mayCloseGoal := false`. If `proofs` is
false, the new goal's proof of the old one has placeholders for the congruence proofs of `∀` and
`→` (see `SimpNoProofs`). -/
def simpTarget (mv : MVarId) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray)
    (proofs : Bool) : MetaM (Option MVarId) := do
  if proofs then
    return (← Meta.simpTarget mv ctx simprocs (mayCloseGoal := false)).1
  mv.withContext do
    mv.checkNotAssigned `simp
    let target ← instantiateMVars (← mv.getType)
    let methods := Simp.mkDefaultMethodsCore simprocs
    let methods := { methods with pre := SimpNoProofs.pre methods.pre }
    let (r, _) ← profileitM Exception "simp" (← getOptions) do
      Simp.main target ctx (methods := methods)
    applySimpResultToTarget mv target r

end Smt.Preprocess
