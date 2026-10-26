/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

module

public import Smt.Translate
public meta import Smt.Translate
public import Smt.Util
public meta import Smt.Util

public meta section

namespace Smt.Translate.Datatype

open Translator Term Lean

/-- Inductive types that have dedicated translators and should not be handled
as generic SMT-LIB datatypes. -/
private def builtinInductives : Std.HashSet Name :=
  Std.HashSet.ofList [
    ``Bool, ``True, ``False,
    ``Or, ``And, ``Iff, ``Exists,
    ``Nat, ``Int, ``String, ``BitVec
  ]

/-- Translate a constructor of an inductive type without indices.
The inductive type itself is marked as a dependency so that the query builder will emit a
`declare-datatypes` command for it. Constructor arguments are translated recursively.

A constructor of an inductive type with type parameters belongs to a parametric datatype, whose
constructors SMT-LIB overloads across its instances. So it is qualified by the sort of the
datatype instance it builds, `(as C (D σ))`, and applied to its fields, as `((as C (D σ)) t₁ ⋯ tₙ)`.

Constructors of indexed inductives, inductives with parameters that are not types, or inductives
whose sort name is already known to SMT-LIB (e.g. `Bool`) are left to other translators or the
fallthrough mechanism. Only fully applied constructors are handled. -/
@[smt_translate] def translateConstructor : Translator := fun e => do
  let some (v, args) ← Lean.Meta.constructorApp? e | return none
  let env ← getEnv
  let inductName := v.induct
  -- Skip types that SMT-LIB already knows about or that have dedicated translators.
  if Util.smtConsts.contains inductName.toString then return none
  if builtinInductives.contains inductName then return none
  -- Only handle non-indexed inductives.
  let some (.inductInfo iVal) := env.find? inductName | return none
  if iVal.numIndices != 0 then return none
  -- Only handle fully applied constructors.
  if args.size != v.numParams + v.numFields then return none
  let params := args.extract 0 v.numParams
  -- Only handle parameters that are types, which become sort parameters.
  unless ← params.allM fun p => return (← Meta.inferType p).isSort do return none
  -- Mark the inductive type as a dependency; the query builder will declare it.
  modify fun st => { st with depConstants := st.depConstants.insert inductName }
  -- Translate constructor arguments and build the application.
  let translatedArgs ← (args.extract v.numParams args.size).mapM applyTranslators!
  let head ← if params.isEmpty then pure (symbolT v.name.toString) else do
    let sort ← applyTranslators! (← Meta.inferType e)
    pure (literalT s!"(as {quoteSymbol v.name.toString} {sort})")
  return some (translatedArgs.foldl appT head)

end Smt.Translate.Datatype
