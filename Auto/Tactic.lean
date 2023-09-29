import Lean
import Auto.Translation
import Auto.Solver.SMT
import Auto.HintDB
import Auto.Embedding.TPTP
open Lean Elab Tactic

initialize
  registerTraceClass `auto.tactic
  registerTraceClass `auto.printLemmas
  registerTraceClass `auto.printProof

namespace Auto

syntax hintelem := term <|> "*"
syntax hints := ("[" hintelem,* "]")?
-- Must be topologically sorted, refer to `Lemma.unfoldConsts`
-- **TODO**: Automatically topological sort
syntax unfolds := ("u[" ident,* "]")?
syntax defeqs := ("d[" ident,* "]")?
syntax autoinstr := ("👍" <|> "👎")?
syntax (name := auto) "auto" autoinstr hints unfolds defeqs : tactic
syntax (name := intromono) "intromono" hints unfolds defeqs : tactic

inductive Instruction where
  | none
  | useSorry

def parseInstr : TSyntax ``Auto.autoinstr → TacticM Instruction
| `(autoinstr|) => return .none
| `(autoinstr|👍) => throwError "Your flattery is appreciated 😎"
| `(autoinstr|👎) => do
  logInfo "I'm terribly sorry. A 'sorry' is sent to you as compensation."
  return .useSorry
| _ => throwUnsupportedSyntax

inductive HintElem where
  -- A user-provided term
  | term     : Term → HintElem
  -- Hint database, not yet supported
  | hintdb   : HintElem
  -- `*` adds all hypotheses in the local context
  -- Also, if `[..]` is not supplied to `auto`, all
  --   hypotheses in the local context are
  --   automatically collected.
  | lctxhyps : HintElem
deriving Inhabited, BEq

def parseHintElem : TSyntax ``hintelem → TacticM HintElem
| `(hintelem| *)       => return .lctxhyps
| `(hintelem| $t:term) => return .term t
| _ => throwUnsupportedSyntax

structure InputHints where
  terms    : Array Term := #[]
  hintdbs  : Array Unit := #[]
  lctxhyps : Bool       := false
deriving Inhabited, BEq

-- Parse `hints` to an array of `Term`, which is still syntax
-- `Array Term`
def parseHints : TSyntax ``hints → TacticM InputHints
| `(hints| [ $[$hs],* ]) => do
  let mut terms := #[]
  let mut lctxhyps := false
  let elems ← hs.mapM parseHintElem
  for elem in elems do
    match elem with
    | .term t => terms := terms.push t
    | .lctxhyps => lctxhyps := true
    | _ => throwError "parseHints :: Not implemented"
  return ⟨terms, #[], lctxhyps⟩
| `(hints| ) => return ⟨#[], #[], true⟩
| _ => throwUnsupportedSyntax

private def defeqUnfoldErrHint :=
  "Note that auto does not accept defeq/unfold hints which" ++
  "are let-declarations in the local context, because " ++
  "let-declarations are automatically unfolded by auto."

def parseUnfolds : TSyntax ``unfolds → TacticM (Array Prep.ConstUnfoldInfo)
| `(unfolds| u[ $[$hs],* ]) => do
  let exprs ← hs.mapM (fun i => do
    let some expr ← Term.resolveId? i
      | throwError "parseUnfolds :: Unknown identifier {i}. {defeqUnfoldErrHint}"
    return expr)
  exprs.mapM (fun expr => do
    let some name := expr.constName?
      | throwError "parseUnfolds :: Unknown declaration {expr}. {defeqUnfoldErrHint}"
    Prep.getConstUnfoldInfo name)
| `(unfolds|) => pure #[]
| _ => throwUnsupportedSyntax

def parseDefeqs : TSyntax ``defeqs → TacticM (Array Name)
| `(defeqs| d[ $[$hs],* ]) => do
  let exprs ← hs.mapM (fun i => do
    let some expr ← Term.resolveId? i
      | throwError "parseDefeqs :: Unknown identifier {i}. {defeqUnfoldErrHint}"
    return expr)
  exprs.mapM (fun expr => do
    let some name := expr.constName?
      | throwError "parseDefeqs :: Unknown declaration {expr}. {defeqUnfoldErrHint}"
    return name)
| `(defeqs|) => pure #[]
| _ => throwUnsupportedSyntax

inductive Result where
  -- Unsatisfiable, witnessed by `e`
  | unsat : (e : Expr) → Result
  -- Satisfiable, witnessed by an assignment to free variables
  | sat : (es : Array (FVarId × Expr)) → Result
  -- Unknown
  | unknown : Result

instance : ToMessageData Result where
  toMessageData : Result → MessageData
  | .unsat e => m!"Result.unsat {e}"
  | .sat es => .compose m!"Result.sat "
    (MessageData.array es (fun (id, e) => m!"{mkFVar id} := {e}"))
  | .unknown => m!"Result.unknown"

def collectLctxLemmas (lctxhyps : Bool) (ngoalAndBinders : Array FVarId) : TacticM (Array Lemma) :=
  Meta.withNewMCtxDepth do
    let fVarIds := (if lctxhyps then (← getLCtx).getFVarIds else ngoalAndBinders)
    let mut lemmas := #[]
    for fVarId in fVarIds do
      let decl ← FVarId.getDecl fVarId
      if ¬ decl.isAuxDecl ∧ (← Meta.isProp decl.type) then
        lemmas := lemmas.push ⟨mkFVar fVarId, ← instantiateMVars decl.type, #[]⟩
    return lemmas

def collectUserLemmas (terms : Array Term) : TacticM (Array Lemma) :=
  Meta.withNewMCtxDepth do
    let mut lemmas := #[]
    for ⟨proof, type, params⟩ in ← terms.mapM Prep.elabLemma do
      if ← Meta.isProp type then
        lemmas := lemmas.push ⟨proof, ← instantiateMVars type, params⟩
      else
        -- **TODO**: Relax condition?
        throwError "invalid lemma {type} for auto, proposition expected"
    return lemmas

def collectDefeqLemmas (names : Array Name) : TacticM (Array Lemma) :=
  Meta.withNewMCtxDepth do
    let lemmas ← names.concatMapM Prep.elabDefEq
    lemmas.mapM (fun (⟨proof, type, params⟩ : Lemma) => do
      let type ← Prep.preprocessTerm (← instantiateMVars type)
      return ⟨proof, type, params⟩)

def unfoldConstAndPreprocessLemma (unfolds : Array Prep.ConstUnfoldInfo) (lem : Lemma) : TacticM Lemma := do
  let mut type ← Prep.preprocessTerm (← instantiateMVars lem.type)
  for ⟨uiname, val, params⟩ in unfolds do
    type := type.replace (fun e =>
      match e with
      | .const name lvls =>
        if name == uiname then
          val.instantiateLevelParams params.data lvls
        else
          .none
      | _ => .none)
  type ← Core.betaReduce (← instantiateMVars type)
  let lem := {lem with type := type}
  let lem ← lem.reorderForallInstDep
  return lem

def traceLemmas (pre : String) (lemmas : Array Lemma) : TacticM Unit := do
  let mut cnt : Nat := 0
  let mut mdatas : Array MessageData := #[]
  for lem in lemmas do
    mdatas := mdatas.push m!"\n{cnt}: {lem}"
    cnt := cnt + 1
  trace[auto.printLemmas] mdatas.foldl MessageData.compose pre

def checkDuplicatedFact (terms : Array Term) : TacticM Unit :=
  let n := terms.size
  for i in [0:n] do
    for j in [i+1:n] do
      if terms[i]? == terms[j]? then
        throwError "Auto does not accept duplicated input terms"

def collectAllLemmas (hintstx : TSyntax ``hints) (unfolds : TSyntax `Auto.unfolds)
  (defeqs : TSyntax `Auto.defeqs) (ngoalAndBinders : Array FVarId) :
  -- The first `Array Lemma` are `Prop` lemmas
  -- The second `Array Lemma` are Inhabitation facts
  TacticM (Array Lemma × Array Lemma) := do
  let inputHints ← parseHints hintstx
  let unfoldInfos ← parseUnfolds unfolds
  let defeqNames ← parseDefeqs defeqs
  let startTime ← IO.monoMsNow
  let lctxLemmas ← collectLctxLemmas inputHints.lctxhyps ngoalAndBinders
  let lctxLemmas ← lctxLemmas.mapM (unfoldConstAndPreprocessLemma unfoldInfos)
  traceLemmas "Lemmas collected from local context:" lctxLemmas
  checkDuplicatedFact inputHints.terms
  let userLemmas ← collectUserLemmas inputHints.terms
  let userLemmas ← userLemmas.mapM (unfoldConstAndPreprocessLemma unfoldInfos)
  traceLemmas "Lemmas collected from user-provided terms:" userLemmas
  let defeqLemmas ← collectDefeqLemmas defeqNames
  let defeqLemmas ← defeqLemmas.mapM (unfoldConstAndPreprocessLemma unfoldInfos)
  traceLemmas "Lemmas collected from user-provided defeq hints:" defeqLemmas
  trace[auto.tactic] "Preprocessing took {(← IO.monoMsNow) - startTime}ms"
  let inhFacts ← Inhabitation.getInhFactsFromLCtx
  let inhFacts ← inhFacts.mapM (unfoldConstAndPreprocessLemma unfoldInfos)
  traceLemmas "Inhabitation lemmas :" inhFacts
  return (lctxLemmas ++ userLemmas ++ defeqLemmas, inhFacts)

-- `ngoal` means `negated goal`
def runAuto (instrstx : TSyntax ``autoinstr) (lemmas : Array Lemma) (inhFacts : Array Lemma) : TacticM Result := do
  let instr ← parseInstr instrstx
  let declName? ← Elab.Term.getDeclName?
  match instr with
  | .none =>
    let afterReify (uvalids : Array UMonoFact) (uinhs : Array UMonoFact) : LamReif.ReifM Expr := (do
      let exportFacts ← LamReif.reifFacts uvalids
      logInfo m!"{TPTP.encodeFacts exportFacts (← LamReif.getTyVal) (← LamReif.getVarVal)}"
      let exportInhs ← LamReif.reifInhabitations uinhs
      let exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
      let exportFacts ← exportFacts.mapM LamReif.skolemizeMostIntoForall
      let exportFacts ← exportFacts.mapM LamReif.validOfExtensionalize
      let exportFacts ← exportFacts.mapM LamReif.validOfBetaReduce
      let exportFacts ← exportFacts.mapM LamReif.validOfRevertAll
      -- ! smt
      -- try
      --   let lamVarTy := (← LamReif.getVarVal).map Prod.snd
      --   let lamEVarTy ← LamReif.getLamEVarTy
      --   let exportLamTerms ← exportFacts.mapM (fun re => do
      --     match re.getValid? with
      --     | .some ([], t) => return t | _ => throwError "runAuto :: Unexpected error")
      --   let commands ← (lamFOL2SMT lamVarTy lamEVarTy exportLamTerms).run'
      --   for cmd in commands do
      --     trace[auto.smt.printCommands] "Command: {cmd}"
      --   Solver.SMT.querySolver commands
      -- catch e =>
      --   trace[auto.smt.result] "SMT invocation failed with {e.toMessageData}"
      -- reconstruction
      let (proof, proofLamTerm, usedEtoms, unsatCore) ← Lam2D.callDuper exportFacts
      trace[auto.printProof] "Duper found proof of {← Meta.inferType proof}"
      LamReif.newAssertion proof proofLamTerm
      let etomInstantiated ← LamReif.validOfInstantiateForall (.valid [] proofLamTerm) (usedEtoms.map .etom)
      let contra ← LamReif.validOfImps etomInstantiated unsatCore
      LamReif.printValuation
      LamReif.printProofs
      Reif.setDeclName? declName?
      let checker ← LamReif.buildCheckerExprFor contra
      let contra ← Meta.mkAppM ``Embedding.Lam.LamThmValid.getFalse #[checker]
      Meta.mkLetFVars ((← Reif.getFvarsToAbstract).map Expr.fvar) contra
      )
    let (proof, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM Expr) do
      let uvalids ← liftM <| Reif.getFacts
      let uinhs ← liftM <| Reif.getInhTys
      let u ← computeMaxLevel uvalids
      (afterReify uvalids uinhs).run' {u := u})
    trace[auto.tactic] "Auto found proof of {← Meta.inferType proof}"
    return .unsat proof
  | .useSorry => return .unsat (← Meta.mkAppM ``sorryAx #[Expr.const ``False [], Expr.const ``false []])

@[tactic auto]
def evalAuto : Tactic
| `(auto | auto $instr $hints $unfolds $defeqs) => withMainContext do
  let startTime ← IO.monoMsNow
  -- Suppose the goal is `∀ (x₁ x₂ ⋯ xₙ), G`
  -- First, apply `intros` to put `x₁ x₂ ⋯ xₙ` into the local context,
  --   now the goal is just `G`
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "evalAuto :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let (lemmas, inhFacts) ← collectAllLemmas hints unfolds defeqs (goalBinders.push ngoal)
    let result ← runAuto instr lemmas inhFacts
    match result with
    | Result.unsat e => do
      IO.println s!"Unsat. Time spent by auto : {(← IO.monoMsNow) - startTime}ms"
      absurd.assign e
    | Result.sat _ => throwError "Sat"
    | Result.unknown => throwError "Unknown"
| _ => throwUnsupportedSyntax

@[tactic intromono]
def evalIntromono : Tactic
| `(intromono | intromono $hints $unfolds $defeqs) => withMainContext do
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "evalAuto :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let (lemmas, _) ← collectAllLemmas hints unfolds defeqs (goalBinders.push ngoal)
    let newMid ← Monomorphization.intromono lemmas absurd
    replaceMainGoal [newMid]
| _ => throwUnsupportedSyntax

end Auto