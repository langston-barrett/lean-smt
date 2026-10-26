/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

module

public import Lean
public meta import Lean
public import Lean.Meta.Tactic.TryThis
public meta import Lean.Meta.Tactic.TryThis

public import Smt.Dsl.Sexp
public meta import Smt.Dsl.Sexp
public import Smt.Reconstruct
public meta import Smt.Reconstruct
public import Smt.Reconstruct.Prop.Lemmas
public meta import Smt.Reconstruct.Prop.Lemmas
public import Smt.Translate.Query
public meta import Smt.Translate.Query
public import Smt.Preprocess
public meta import Smt.Preprocess
public import Smt.Util
public meta import Smt.Util

public meta section

namespace Smt

open Lean hiding Command
open Elab Tactic Qq
open Smt Translate Query Reconstruct Util

/-- Configuration options for the SMT tactic. -/
structure Config where
  /-- The timeout for the SMT solver in seconds. -/
  timeout : Option Nat := .none
  /-- Whether to enable native components for proof reconstruction. Speeds up normalization and
      reduction proof steps. However, it adds the Lean compiler to the trusted code base. -/
  native : Bool := false
  /-- Whether to introduce binders automatically. Disable to generate a more faithful SMT-LIB query
      or if introducing binders causes undesired behavior (e.g., not eliminating let expressions).
      Ignored if monomorphization is enabled. -/
  intros : Bool := true
  /-- Whether to monomorphize the Lean goal before sending it to the SMT solver. The monomorphization
      step reduces the goal from Lean's dependent type theory to a simpler, first-order logic. -/
  mono : Bool := false
  /-- Whether to normalize the Lean goal before sending it to the SMT solver. The normalization
      step performs unconditional rewrites to ensure that the goal is in a standard form suitable
      for SMT solving. -/
  normalize : Bool := true
  /-- Whether to embed subtypes (e.g., `Nat`, `Bool`, `Rat`) into types understood by the SMT solver. -/
  embeddings : Bool := true
  /-- Whether to embed `Bool` values into `Prop`. Only takes effect when `embeddings` is enabled.
      **Warning**: disabling this can make proof reconstruction or unsat-core extraction fail, so it
      is currently only recommended together with `trust`. -/
  embedBool : Bool := true
  /-- Whether to trust the result of the SMT solver. Closes the current goal with a `sorry` if the
      SMT solver returns `unsat`. **Warning**: use with caution, as this may lead to unsoundness.
      Additionally adds the translation from Lean to SMT to the trusted code base, which is not
      always sound. -/
  trust : Bool := false
  /-- Whether to show a potential counter-example when the SMT solver returns `sat`. -/
  model : Bool := false
  /-- Just show the SMT query without invoking a solver. Useful for debugging. -/
  showQuery : Bool := false
  /-- Options to pass to the solver, in addition to the default ones. -/
  extraSolverOptions : List (String × String) := []
deriving Inhabited, Repr

/-- The elaboration context in which expressions stored in an SMT model are meaningful. -/
structure ModelContext where
  ci : Elab.ContextInfo
  lctx : LocalContext
  linsts : LocalInstances
deriving TypeName

/-- Save the current elaboration and local contexts for later model processing. -/
def ModelContext.save : MetaM ModelContext :=
  return {
    ci := { ← CommandContextInfo.save with }
    lctx := ← getLCtx
    linsts := ← Meta.getLocalInstances
  }

/-- Run a metaprogram using the elaboration and local contexts saved with an SMT model. -/
def ModelContext.runMetaM (ctx : ModelContext) (x : MetaM α) : IO α :=
  ctx.ci.runMetaM {} <| Meta.withLCtx ctx.lctx ctx.linsts x

/-- A reconstructed SMT model together with the context required to process its expressions. -/
structure Model where
  /-- Context information for free variables occurring in the model. -/
  ctx : ModelContext
  /-- Interpretations of uninterpreted sorts, represented as pairs of sorts and finite types. -/
  sorts : Array (Expr × Expr)
  /-- Interpretations of constants and functions. -/
  values : Array (Expr × Expr)

/-- All model interpretations in the legacy order: sorts followed by values. -/
def Model.entries (model : Model) : Array (Expr × Expr) :=
  model.sorts ++ model.values

def Model.isEmpty (model : Model) : Bool :=
  model.sorts.isEmpty && model.values.isEmpty

inductive Result where
  | sat (model : Option Model)
  | unsat (mvs : List MVarId) (usedHints : Array Expr)
  | unknown (reason : String)

/-- An event produced while an `smt` call is running. Events for one call are emitted in this
order when enabled: `queryString`, `rawResult`, then `result`. An `exception` is the terminal event
instead of `result` when the call throws. -/
inductive AsyncOutput where
  | queryString (query : String)
  | rawResult (raw : Except cvc5.Error cvc5Result)
  | result (result : Result)
  | exception (ex : Exception)
deriving Inhabited

/-- Configuration and call numbering for the optional asynchronous event stream. -/
structure AsyncState where
  /-- User-provided name shared by related calls. -/
  name : Name := `smt
  /-- Index assigned to the next call on this stream. -/
  index : Nat := 0
  sendQuery : Bool := false
  sendRawResult : Bool := false
  sendResult : Bool := true
  /-- Caller-owned channel. `smt` sends events but never closes it. -/
  ch : Option (Std.CloseableChannel ((Name × Nat) × AsyncOutput)) := none
deriving Inhabited

/-- Scoped asynchronous state used by `smt`. With no initialized channel, the tactic behaves as
before and does not mutate the environment. -/
initialize asyncState : SimpleScopedEnvExtension AsyncState AsyncState ←
  registerSimpleScopedEnvExtension {
    name := `asyncState
    initial := default
    addEntry := fun _ state => state
  }

/-- Initialize an asynchronous SMT event stream. If `ch` is supplied, it remains owned by the
caller; otherwise a fresh caller-owned channel is returned. Reinitializing resets call indices to
zero. The defaults match Veil's existing use: only reconstructed results are sent. -/
def initAsyncState [Monad m] [MonadEnv m] [MonadLiftT BaseIO m]
    [MonadLiftT (ST IO.RealWorld) m] [MonadFinally m]
    (name : Name)
    (ch : Option (Std.CloseableChannel ((Name × Nat) × AsyncOutput)) := none)
    (sendQuery := false) (sendRawResult := false) (sendResult := true) :
    m (Std.CloseableChannel ((Name × Nat) × AsyncOutput)) := do
  let ch ← match ch with
    | some ch => pure ch
    | none => Std.CloseableChannel.new
  Lean.modifyEnv (asyncState.modifyState · fun _ => {
    name, index := 0, sendQuery, sendRawResult, sendResult, ch := some ch
  })
  return ch

private def getAsyncStateAndIncreaseIndex : MetaM AsyncState := do
  let state := asyncState.getState (← getEnv)
  if state.ch.isSome then
    Lean.modifyEnv (asyncState.modifyState · fun _ => { state with index := state.index + 1 })
  return state

private def AsyncState.send (state : AsyncState) (id : Name × Nat) (output : AsyncOutput) :
    MetaM Unit :=
  state.ch.forM fun ch => Std.CloseableChannel.Sync.send ch (id, output)

private def AsyncState.sendException (state : AsyncState) (id : Name × Nat)
    (ex : Exception) : MetaM Unit := do
  -- If the caller closed the channel early, preserve the original exception instead of replacing
  -- it with a channel error.
  try state.send id (.exception ex) catch _ => pure ()

def genUniqueFVarNames : MetaM (Std.HashMap FVarId String × Std.HashMap String Expr) := do
  let lCtx ← getLCtx
  let st : NameSanitizerState := { options := {}}
  let (lCtx, _) := (lCtx.sanitizeNames st).run
  return lCtx.getFVarIds.foldl (init := ({}, {})) fun (m₁, m₂) fvarId =>
    let m₁ := m₁.insert fvarId (lCtx.getRoundtrippingUserName? fvarId).get!.toString
    let m₂ := m₂.insert (lCtx.getRoundtrippingUserName? fvarId).get!.toString (.fvar fvarId)
    (m₁, m₂)

def prepareSmtQuery (hs : List Expr) (fvNames : Std.HashMap FVarId String) : MetaM (List Command) := do
  Query.generateQuery hs fvNames

def smt (cfg : Config) (mv : MVarId) (hs : Array Expr) : MetaM Result := mv.withContext do
  let asyncState ← getAsyncStateAndIncreaseIndex
  let asyncId := (asyncState.name, asyncState.index)
  let finish (result : Result) : MetaM Result := do
    if asyncState.sendResult then
      asyncState.send asyncId (.result result)
    return result
  try
  -- 0. Create a duplicate goal to preserve the original goal.
  let goalType : Q(Prop) ← mv.getType
  let mv₀ := (← Meta.mkFreshExprMVar (← mv.getType)).mvarId!
  -- 1. Cleanup goal.
  let mv₀ ← mv₀.cleanup (← hs.foldlM (fun s h => return (← (Expr.collectFVars h).run s).snd) {}).fvarIds
  trace[smt.preprocess] "after cleanup: {mv₀}"
  mv₀.withContext do
  -- 2. Preprocess the hints and goal.
  let steps := if cfg.mono then #[Preprocess.mono] else #[Preprocess.pushHintsToCtx] ++
              (if cfg.intros then #[Preprocess.intros] else #[]) ++ #[Preprocess.negateGoal]
  -- Under `trust`, the original goal is admitted, so the preprocessing proofs are not needed.
  let steps := if cfg.normalize then steps.push (Preprocess.normalizeWithProofs !cfg.trust) else steps
  let steps :=
    if cfg.embeddings then
      steps.push <| Preprocess.embeddingWithConfig { embedBool := cfg.embedBool, proofs := !cfg.trust }
    else
      steps
  let ⟨map, hs₁, mv₁⟩ ← Preprocess.applySteps mv₀ hs steps
  mv₁.withContext do
  -- 3. Generate the SMT query.
  let (fvNames₁, fvNames₂) ← genUniqueFVarNames
  let cmds ← prepareSmtQuery hs₁.toList fvNames₁
  let cmds := .setLogic "ALL" :: cmds
  let query := Command.cmdsAsQuery (cmds ++ [.checkSat])
  if asyncState.sendQuery then
    asyncState.send asyncId (.queryString query)
  if cfg.showQuery then
    mv.withContext do logInfo m!"goal: {goalType}\n\nquery:\n{query}"
    -- Return original goal.
    return ← finish (.unsat [mv] hs₁)
  else
    mv.withContext do trace[smt] "goal: {goalType}"
    trace[smt] "\nquery:\n{query}"
  -- 4. Run the solver.
  let options := defaultSolverOptions ++ (if cfg.trust then [] else [("produce-proofs", "true")]) ++ cfg.extraSolverOptions
  let res ← solve (Command.cmdsAsQuery cmds) cfg.timeout (!cfg.trust) options
  -- trace[smt] "\nresult: {res}"
  if asyncState.sendRawResult then
    asyncState.send asyncId (.rawResult res)
  match res with
  | .error e =>
    -- 5a. Print error reason.
    trace[smt.solve] "\nerror:\n{repr e}\n"
    throwError e.toString
  | .ok (.unknown r) =>
    -- 5b. Print unknown reason.
    trace[smt.solve] "\nunknown reason:\n{r}\n"
    finish (.unknown r.toString)
  | .ok (.unsat pf uc) =>
    if cfg.trust then
      -- 6. Trust the result by admitting original goal.
      -- We make this a non-synthetic `sorry` because morally it is requested
      -- by the user rather than showing a tactic failure.
      mv.admit (synthetic := false)
      return ← finish (.unsat [] hs)
    -- 5.c Reconstruct unsat core proofs.
    let ctx := { userNames := fvNames₂, native := cfg.native }
    let (uc, _) ← (uc.mapM Reconstruct.reconstructTerm).run ctx {}
    trace[smt] "unsat core: {uc}"
    let ts₁ ← hs₁.mapM Meta.inferType
    let uc ← uc.filterMapM fun p => ts₁.findIdxM? (Meta.isDefEq p)
    let uc := uc.filterMap fun p => (hs₁[p]?)
    let uc := uc.filterMap (map[·]?)
    let uc := hs.filter uc.flatten.contains
    -- 7. Reconstruct proof.
    let some pf := pf | throwError "failed to reconstruct proof for unsat result"
    let (_, ps, p, hp, mvs) ← reconstructProof pf ctx
    let mv₂ ← mv₁.assert (← mkFreshId) p hp
    let ⟨_, mv₃⟩ ← mv₂.intro1
    let gs ← mv₃.apply (← Meta.mkAppOptM ``Prop.implies_false_of_not_and #[listExpr ps q(Prop)])
    mv₃.withContext (gs.forM (·.assumption))
    mv.assign (.mvar mv₀)
    finish (.unsat mvs uc)
  | .ok (.sat model) =>
    -- 5d. Return potential counter-example.
    if !cfg.model then
      return ← finish (.sat none)
    let (uss, es) := model.iss.unzip
    let cs := es.map Array.size
    let sortCard := Std.HashMap.insertMany ∅ (uss.zip cs)
    let ctx := { userNames := fvNames₂, sortCard := sortCard, native := cfg.native }
    let (uss', _) ← (uss.mapM Reconstruct.reconstructSort).run ctx {}
    let uss' := uss'.map fun us => (map[us]?.getD #[us])[0]?.getD us
    let cs' := cs.map (fun n => .app (.const ``Fin []) (toExpr n))
    let state := { sortCache := Std.HashMap.insertMany ∅ (uss.zip cs') }
    let (ufs, vs) := model.ifs.unzip
    let (ufs', state) ← (ufs.mapM Reconstruct.reconstructTerm).run ctx state
    let ufs' := ufs'.map fun uf => (map[uf]?.getD #[uf])[0]?.getD uf
    let (vs', _) ← (vs.mapM Reconstruct.reconstructTerm).run ctx state
    let model := {
      ctx := ← mv₀.withContext ModelContext.save
      sorts := uss'.zip cs'
      values := ufs'.zip vs'
    }
    finish (.sat (.some model))
  catch ex =>
    asyncState.sendException asyncId ex
    throw ex

namespace Tactic

syntax smtStar := "*"

syntax smtHintElem := smtStar <|> term

syntax smtHints := (" [" withoutPosition(smtHintElem,*,?) "]")?

open Lean.Parser.Tactic in
/-- `smt` converts the current goal into an SMT query and checks if it is
satisfiable. By default, `smt` generates the minimum valid SMT query needed to
assert the current goal. However, that is not always enough:
```lean
theorem modus_ponens (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt
```
For the theorem above, `smt` generates the query below:
```smt2
(declare-const q Bool)
(assert (not q))
(check-sat)
```
which is missing the hypotheses `hp` and `hpq` required to prove the theorem. To
pass hypotheses to the solver, use `smt [h₁, h₂, ..., hₙ]` syntax:
```lean
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt [hp, hpq]
```
The tactic then generates the query below:
```smt2
(declare-const q Bool)
(assert (not q))
(declare-const p Bool)
(assert p)
(assert (=> p q))
(check-sat)
```
The tactic also supports the `*` wildcard hint, which means "all hypotheses".
So, the following also works:
```lean
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt [*]
```
The tactic can be configured with additional options. For example, to set a
timeout of 1 second for the SMT solver, use:
```lean
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt (timeout := .some 1) [*]
```
Please take a look at the `Smt.Config` structure for more options.
-/
syntax (name := smt) "smt " optConfig smtHints : tactic

open Lean.Parser.Tactic in
/--
`smt?` takes the same arguments as `smt`, but reports an equivalent call to
`smt` that would be sufficient to close the goal. This is useful for reducing
the size of the hints in a local invocation to speed up processing.
```
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  smt? -- prints "Try this: simp only [ite_true]"
```
-/
syntax (name := smtTrace) "smt?" optConfig smtHints : tactic

open Lean.Parser.Tactic in
/-- `smt_show` is short-hand for `smt +showQuery`. -/
macro "smt_show " c:optConfig h:smtHints : tactic => do
  let `(optConfig| $cs*) := c | Macro.throwUnsupported
  match h with
  | `(smtHints| )        => `(tactic| (smt +showQuery $cs*))
  | `(smtHints| [$hs,*]) => `(tactic| (smt +showQuery $cs* [$hs,*]))
  | _                    => Macro.throwUnsupported

declare_config_elab elabConfig Smt.Config

/-- If `nm` names a non-Prop definition with auto-generated equation lemmas `nm.eq_1`, `nm.eq_2`, …,
return those as expressions.  Returns an empty array for theorems/props or missing lemmas. -/
private def getEqLemmas (nm : Name) : MetaM (Array Expr) := do
  let env ← getEnv
  let some info := env.find? nm | return #[]
  -- Only expand non-Prop definitions (i.e., functions, not theorems)
  if info.type.isProp then return #[]
  -- Use Lean's proper API to retrieve the auto-generated equation lemmas.
  let some eqNames ← Lean.Meta.getEqnsFor? nm | return #[]
  return eqNames.map fun eqNm =>
    let lvls := (env.find? eqNm).map (·.levelParams.map .param) |>.getD []
    .const eqNm lvls

def elabSmtHintElem : TSyntax ``smtHintElem → TacticM (Array (Expr × (TSyntax ``smtHintElem)) × Array Expr)
  | `(smtHintElem| *) => do
    let fvs ← Smt.Preprocess.getPropHyps
    let hs := fvs.map Expr.fvar
    let lctx ← getLCtx
    let ss : Array (TSyntax ``smtHintElem) ← fvs.mapM fun fv => do
      if let some ldecl := lctx.find? fv then
        if !ldecl.userName.isInaccessibleUserName && !ldecl.userName.hasMacroScopes &&
            (lctx.findFromUserName? ldecl.userName).get!.fvarId == ldecl.fvarId then
          `(smtHintElem| $(mkIdent ldecl.userName):ident)
        else
          `(smtHintElem| *)
      else
        `(smtHintElem| *)
    return (hs.zip ss, hs)
  | `(smtHintElem| $h:term) => do
    -- If the hint is a bare identifier naming a non-Prop definition, expand it to its
    -- auto-generated equation lemmas (nm.eq_1, nm.eq_2, …) automatically.
    let eqExprs ← do
      if h.raw.isIdent then
        let nm := h.raw.getId
        let env ← getEnv
        if let some info := env.find? nm then
          if !info.type.isProp then
            getEqLemmas nm
          else pure #[]
        else pure #[]
      else pure #[]
    if !eqExprs.isEmpty then
      let pairs ← eqExprs.mapM fun e => return (e, ← `(smtHintElem| $h:term))
      return (pairs, eqExprs)
    -- Fall through: treat as a regular lemma (prop hypothesis or theorem).
    let h' ← Auto.Prep.elabLemma h (.leaf s!"❰{h}❱")
    return (#[(h'.proof, ← `(smtHintElem| $h:term))], #[h'.proof])
  | _ => throwUnsupportedSyntax

def elabHints : TSyntax ``smtHints → TacticM (Std.HashMap Expr (TSyntax ``smtHintElem) × Array Expr)
  | `(smtHints| [ $[$hs],* ]) => withMainContext do
    hs.foldlM (init := ({}, #[])) fun (map, acc) h => do
      let (m, a) ← elabSmtHintElem h
      return (map.insertMany m, acc ++ a)
  | `(smtHints| ) => return ({}, #[])
  | _ => throwUnsupportedSyntax

def evalSmtCore (cfg : TSyntax ``Parser.Tactic.optConfig) (hs : TSyntax ``smtHints) := withMainContext do
  let cfg ← elabConfig cfg
  let mv ← Tactic.getMainGoal
  let (map, hs) ← elabHints hs
  let res ← Smt.smt cfg mv hs
  match res with
    | .sat none =>
      throwError "unable to prove goal, either it is false or you need to provide more facts. Try adding '+model' config option to display a potential counter-example (experimental)."
    | .sat (.some model) =>
      if model.isEmpty then
        throwError "unable to prove goal, either it is false or you need to provide more facts. Could not produce a counter-example. Try introducing variables into the local context to get a counter-example."
      else
        let mut md := m!""
        for (v, t) in model.entries do
          md := md ++ m!"\n  {v} = {t}"
        throwError "unable to prove goal, either it is false or you need to provide more facts. Here is a potential counter-example:\n{md}"
    | .unsat mvs uc =>
      Tactic.replaceMainGoal mvs
      let uc := uc.filterMap map.get?
      let uc := uc.toList.eraseDups.toArray
      return uc
    | .unknown r =>
      throwError "unable to prove goal. Try providing more hints. Reason: {r}"

@[tactic smt] def evalSmt : Tactic := fun stx => match stx with
  | `(tactic| smt $cfg:optConfig $hs:smtHints) => do
    _ ← evalSmtCore cfg hs
  | _ => throwUnsupportedSyntax

@[tactic smtTrace] def evalSmtTrace : Tactic := fun stx => withMainContext do
  match stx with
  | `(tactic| smt?%$tk $cfg:optConfig $hs:smtHints) => do
    let uc ← evalSmtCore cfg hs
    let stx ← if uc.isEmpty then `(tactic| smt%$tk) else `(tactic| smt%$tk $cfg [$uc,*])
    Lean.Meta.Tactic.TryThis.addSuggestion tk stx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

end Smt.Tactic
