/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

module

public import Smt.Reconstruct
public meta import Smt.Reconstruct

public meta section

namespace Smt.Reconstruct.Datatype

open Lean Meta Qq

/-- Names of types that already have dedicated sort/term/proof reconstructors
and should not be handled by the generic datatype reconstructor. -/
private def builtinTypeNames : Std.HashSet Name :=
  Std.HashSet.ofList [
    ``Bool, `Prop, ``True, ``False,
    ``Or, ``And, ``Iff, ``Exists,
    ``Nat, ``Int, `Rat, `Real,
    ``String, ``BitVec
  ]

/-- Return `true` when the name (or its prefix for a constructor) belongs to a
type with dedicated built-in reconstruction support. -/
private def isBuiltinName (n : Name) : Bool :=
  builtinTypeNames.contains n ||
  -- Also catch constructor names like `Bool.true`, `Nat.zero`, etc.
  match n with
  | .str p _ => builtinTypeNames.contains p
  | _ => false

-- Strip SMT-LIB2 pipe quoting (|name|) from a symbol if present.
private def stripSMTPipes (s : String) : String :=
  if s.startsWith "|" && s.endsWith "|" then (s.drop 1 |>.dropEnd 1).toString else s

/-- The symbol of a constructor, which cvc5 prints qualified by its sort, `(as C (D σ))`, when it
belongs to a parametric datatype. -/
private def unqualify (s : String) : String :=
  if !s.startsWith "(as " then s else
  let rest := (s.drop 4).toString
  if rest.startsWith "|" then
    -- A quoted symbol ends at the next `|`.
    "|" ++ ((rest.drop 1).takeWhile (· != '|')).toString ++ "|"
  else (rest.takeWhile fun c => !c.isWhitespace && c != ')').toString

private def getFVarOrConstExpr! (n : String) : ReconstructM Expr := do
  match (← read).userNames[n]? with
  | some e => return e
  | none   => match (← getLCtx).findFromUserName? n.toName with
    | some d => return d.toExpr
    | none   =>
      let c ← getConstInfo n.toName
      return .const c.name (c.numLevelParams.repeat (.zero :: ·) [])

/-- Whether `s` is a datatype sort. cvc5 gives an instance of a parametric datatype, such as
`(Option Int)`, an internal kind rather than `DATATYPE_SORT`. -/
private def isDatatypeSort (s : cvc5.Sort) : Bool :=
  s.getKind! == .DATATYPE_SORT || (s.isInstantiated && s.isDatatype)

/-- A datatype's type argument: SMT-LIB's `Bool` is `Bool` there, not a
proposition, since a datatype's parameters are types of data, as in
`Option Bool`. -/
private def reconstructParameter (s : cvc5.Sort) : ReconstructM Expr :=
  if s.isBoolean then return mkConst ``Bool else reconstructSort s

@[smt_sort_reconstruct] def reconstructDatatypeSort : SortReconstructor := fun s => do
  unless isDatatypeSort s do return none
  let name := s.getDatatype!.getName!
  if isBuiltinName name.toName then return none
  -- An instance of a parametric datatype is the inductive type applied to its parameters.
  let params := if s.isInstantiated then s.getInstantiatedParameters! else #[]
  return mkAppN (← getFVarOrConstExpr! name) (← params.mapM reconstructParameter)

/-- `arg`, a reconstructed SMT Boolean, as the next argument of `f`: the `Bool`
that it stands for where `f` takes a `Bool`, and itself where it takes a
proposition. -/
private def boolField (f arg : Expr) : MetaM Expr := do
  let .forallE _ d _ _ ← whnf (← inferType f) | return arg
  unless d.isConstOf ``Bool do return arg
  if arg.isConstOf ``True then return mkConst ``Bool.true
  if arg.isConstOf ``False then return mkConst ``Bool.false
  mkDecide arg

@[smt_term_reconstruct] def reconstructDatatypeTerm : TermReconstructor := fun t => do
  match t.getKind! with
  | .APPLY_CONSTRUCTOR =>
    -- t[0]! is the constructor symbol. It has INTERNAL_KIND in cvc5 (even for non-zero-arity),
    -- so we look it up by name instead of calling reconstructTerm recursively.
    -- toString may include SMT-LIB pipe escaping (e.g., "|mynat'.succ|"), so strip it.
    let ctorName := stripSMTPipes (unqualify t[0]!.toString)
    if isBuiltinName ctorName.toName then return none
    let mut curr ← getFVarOrConstExpr! ctorName
    -- A constructor of a parametric datatype takes the instance's parameters first.
    let sort := t.getSort!
    if sort.isInstantiated then
      curr := mkAppN curr (← sort.getInstantiatedParameters!.mapM reconstructParameter)
    for i in [1:t.getNumChildren] do
      let arg ← reconstructTerm t[i]!
      -- SMT-LIB's `Bool` is reconstructed as a proposition, but a field of type
      -- `Bool` takes a Boolean: `Value.Boolean false`, not `Value.Boolean False`.
      let arg ← if t[i]!.getSort!.isBoolean then boolField curr arg else pure arg
      curr := .app curr arg
    return curr
  | _ => return none

/-- Build a Lean proof of `(t = s) = False` where `t` and `s` are
distinct constructors of the same inductive type. Uses the `noConfusion`
principle that Lean auto-generates for every inductive type, which `mkNoConfusion` applies to the
type's parameters, if any. -/
private def proveConsClash (t s : Expr) : MetaM Expr := do
  let heq ← mkEq t s
  -- Forward: (t = s) → False  via noConfusion with motive False
  let fwd ← withLocalDeclD `h heq fun h => do
    let nc ← mkNoConfusion (mkConst ``False) h
    mkLambdaFVars #[h] nc
  -- Backward: False → (t = s)  via False.elim
  let bwd ← withLocalDeclD `h (mkConst ``False) fun h => do
    let fe ← mkAppOptM ``False.elim #[some heq, some h]
    mkLambdaFVars #[h] fe
  let iff_pf ← mkAppM ``Iff.intro #[fwd, bwd]
  mkAppM ``propext #[iff_pf]

def reconstructRewrite (pf : cvc5.Proof) : ReconstructM (Option Expr) := do
  match pf.getRewriteRule! with
  | .MACRO_DT_CONS_EQ
  | .DT_CONS_EQ_CLASH =>
    let result := pf.getResult
    -- Only handle the "clash" case: (t = s) = false (distinct constructors)
    if result[1]!.getKind! == .CONST_BOOLEAN && !result[1]!.getBooleanValue! then
      let sort := result[0]![0]!.getSort!
      if isDatatypeSort sort && isBuiltinName sort.getDatatype!.getName!.toName then
        return none
      let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort sort
      let t : Q($α) ← reconstructTerm result[0]![0]!
      let s : Q($α) ← reconstructTerm result[0]![1]!
      addTac q(($t = $s) = False) fun mv => do
        let proof ← mv.withContext (proveConsClash t s)
        mv.assign proof
    else
      return none
  | _ => return none

/-- Build a Lean proof of `¬(t = s)` where `t` and `s` are distinct constructors.
Uses the `noConfusion` principle: `fun h : t = s => noConfusion False t s h`, through
`mkNoConfusion`, which supplies the type's parameters, if any. -/
private def proveDistinctValues (t s : Expr) : MetaM Expr := do
  let heq ← mkEq t s
  withLocalDeclD `h heq fun h => do
    let nc ← mkNoConfusion (mkConst ``False) h
    mkLambdaFVars #[h] nc

@[smt_proof_reconstruct] def reconstructDatatypeProof : ProofReconstructor := fun pf => do
  match pf.getRule with
  | .DSL_REWRITE
  | .THEORY_REWRITE => reconstructRewrite pf
  | .DISTINCT_VALUES =>
    let sort := pf.getArguments[0]!.getSort!
    if isDatatypeSort sort && isBuiltinName sort.getDatatype!.getName!.toName then
      return none
    let (u, (α : Q(Sort u))) ← reconstructSortLevelAndSort sort
    let t : Q($α) ← reconstructTerm pf.getArguments[0]!
    let s : Q($α) ← reconstructTerm pf.getArguments[1]!
    addTac q($t ≠ $s) fun mv => do
      let proof ← mv.withContext (proveDistinctValues t s)
      mv.assign proof
  | _ => return none

end Smt.Reconstruct.Datatype
