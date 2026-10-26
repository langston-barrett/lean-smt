/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp
public import Smt.Preprocess.Basic
public meta import Smt.Preprocess.Basic
public import Smt.Preprocess.Embedding.Attribute
public meta import Smt.Preprocess.Embedding.Attribute
public import Smt.Preprocess.SimpNoProofs
public meta import Smt.Preprocess.SimpNoProofs

public meta section

private def Lean.Expr.contains (e : Expr) (p : Expr → Bool) : Bool :=
  (e.find? p).isSome

namespace Smt.Preprocess

open Lean

/-- Selects which base types the embedding step lifts into SMT-friendly types. -/
structure EmbeddingConfig where
  /-- Whether to embed `Nat` into `Int`. -/
  embedNat : Bool := true
  /-- Whether to embed `Rat` into `Real`. Only takes effect when `Real` is available. -/
  embedRat : Bool := true
  /-- Whether to embed `Bool` into `Prop`. -/
  embedBool : Bool := true
  /-- Whether to build the proof that the embedded goal implies the original one. If not, the
      proof has placeholders (see `SimpNoProofs`), so the goal must be admitted. -/
  proofs : Bool := true

/-- The base types selected by `cfg`, in embedding order. -/
def EmbeddingConfig.baseTypes (cfg : EmbeddingConfig) : MetaM (Array Name) := do
  let mut bts := #[]
  if cfg.embedNat then
    bts := bts.push ``Nat
  if cfg.embedRat && (← getEnv).contains `Real then
    bts := bts.push ``Rat
  if cfg.embedBool then
    bts := bts.push ``Bool
  return bts

def hasType (e : Expr) (p : Expr → Bool) : Bool :=
  match e with
  | .forallE _ t b _ => p t || hasType b p
  | _                => p e

def hasReturnType (e : Expr) (p : Expr → Bool) : Bool :=
  match e with
  | .forallE _ _ b _ => hasReturnType b p
  | _                => p e

def embeddingWithConfig (cfg : EmbeddingConfig) (mv : MVarId) (hs : Array Expr) : MetaM Result := mv.withContext do
  -- Find all free vars to revert in `hs` and `mv`.
  let ts ← hs.mapM Meta.inferType
  let ⟨_, _, fvs⟩ := (ts.push (← mv.getType)).foldl Lean.collectFVars {}
  let fvs ← Meta.sortFVarIds fvs
  -- Check if we need to do anything.
  let bts ← cfg.baseTypes
  if bts.isEmpty then
    return ⟨{}, hs, mv⟩
  let fvts ← fvs.mapM FVarId.getType
  if !(fvts ++ ts.push (← mv.getType)).any (·.contains ((bts.map (.const · [])).contains ·)) then
    return ⟨{}, hs, mv⟩
  -- Find the embedding simp theorems.
  let some thmsExt ← Meta.getSimpExtension? `embedding | throwError "embedding simp extension not found"
  let some procsExt ← Meta.Simp.getSimprocExtension? `embedding | throwError "embedding simproc extension not found"
  let simpTheorems := #[← thmsExt.getTheorems]
  let simpProcs := #[← procsExt.getSimprocs]
  -- Assert all hypotheses that are not free vars.
  let (hs₁, hs₂) := hs.partition Expr.isFVar
  let ts₂ ← hs₂.mapM Meta.inferType
  let as₂ : Array Meta.Hypothesis := (hs₂.zip ts₂).map fun (h, t) => { userName := .anonymous, type := t, value := h }
  let (fvs₂, mv) ← mv.assertHypotheses as₂
  -- Build map from new hypotheses to old ones.
  let inverseMap₁ : Std.HashMap Expr Expr := hs.foldl (init := {}) fun map h =>
    match hs₂.findIdx? (· == h) with
    | some idx => map.insert h (.fvar fvs₂[idx]!)
    | none => map.insert h h
  -- Revert free vars in `hs` and `mv`.
  let fvs ← Meta.sortFVarIds <| fvs ++ hs₁.map Expr.fvarId! ++ fvs₂
  let (fvs, mv) ← mv.revert fvs true
  -- Simplify the goal using the embedding theorems.
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ctx ← Meta.Simp.mkContext { zeta := false, singlePass := true } simpTheorems congrTheorems
  let some mv ← simpTarget mv ctx simpProcs cfg.proofs | throwError "[embedding] simplification failed"
  -- Extend `fvs` to account for `nonneg` assumptions.
  let bts := bts.filter (· != ``Bool) -- Do not consider `Bool` for assumptions.
  let mut fvs' : Array (Option FVarId) := #[]
  for fv in fvs do
    fvs' := fvs'.push (some fv)
    let t ← fv.getType
    if hasReturnType t ((bts.map (.const · [])).contains ·) then
      fvs' := fvs'.push none
  -- Re-introduce all free vars (and their `nonneg` assumptions).
  let (fvs'', mv) ← mv.introNP fvs'.size
  -- Compose the final map from new free vars to old ones.
  -- We do not need to map `nonneg` assumptions. Since `nonneg` assumptions are auxiliary,
  -- We can always provide all of them to the SMT solver without affecting the unsat core.
  let (inverseMap₂, hs') := (fvs'.zip fvs'').foldl (init := ({}, #[])) fun (map, hs') (of, to) =>
    match of with
    | some of => (map.insert (.fvar of) (.fvar to), hs')
    | none    => (map, hs'.push (.fvar to))
  let inverseMap := compose inverseMap₁ inverseMap₂
  let hs' := hs' ++ hs.map fun h => inverseMap[h]?.getD h
  let map := (inverse inverseMap).fold (init := {}) fun map k v => map.insert k #[v]
  return { map := map, hs := hs', mv }
where
  compose (m₁ m₂ : Std.HashMap Expr Expr) : Std.HashMap Expr Expr :=
    m₁.fold (init := m₂) fun map k v =>
      map.insert k (map[v]?.getD v)
  inverse (m : Std.HashMap Expr Expr) : Std.HashMap Expr Expr :=
    m.fold (init := {}) fun map k v =>
      map.insert v k

def embedding (mv : MVarId) (hs : Array Expr) : MetaM Result :=
  embeddingWithConfig {} mv hs

end Smt.Preprocess
