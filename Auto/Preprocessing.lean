import Lean
import Auto.Util.AbstractMVars
open Lean Meta Elab Tactic

initialize
  registerTraceClass `auto.Prep

namespace Auto

structure Lemma where
  proof  : Expr       -- Proof of the lemma
  type   : Expr       -- The statement of the lemma
  params : Array Name -- Universe Levels  

namespace Prep

/-- This function is expensive and should only be used in preprocessing -/
partial def preprocessLemma (fact : Expr) : MetaM Expr := do
  let red (e : Expr) : MetaM TransformStep := do
    let e := e.consumeMData
    let e ← Meta.whnf e
    return .continue e
  -- Reduce
  let fact ← Meta.withTransparency .instances <| Meta.transform fact (pre := red) (usedLetOnly := false)
  return fact

-- **TODO**: Review
-- Advise: For each recursive function (not only recursors)
--   `f : {recty} → ...`, apply
--   `f` to each constructor of {recty} and beta reduce!
def addRecAsLemma (recVal : RecursorVal) : TacticM (Array Lemma) := do
  let some (.inductInfo indVal) := (← getEnv).find? recVal.getInduct
    | throwError "Expected inductive datatype: {recVal.getInduct}"
  let expr := mkConst recVal.name (recVal.levelParams.map Level.param)
  let res ← forallBoundedTelescope (← inferType expr) recVal.getMajorIdx fun xs _ => do
    let expr := mkAppN expr xs
    indVal.ctors.mapM fun ctorName => do
      let ctor ← mkAppOptM ctorName #[]
      let (proof, eq) ← forallTelescope (← inferType ctor) fun ys _ => do
        let ctor := mkAppN ctor ys
        let expr := mkApp expr ctor
        let some redExpr ← reduceRecMatcher? expr
          | throwError "Could not reduce recursor application: {expr}"
        let redExpr ← Core.betaReduce redExpr
        let eq ← mkEq expr redExpr
        let proof ← mkEqRefl expr
        return (← mkLambdaFVars ys proof, ← mkForallFVars ys eq)
      let proof ← instantiateMVars (← mkLambdaFVars xs proof)
      let eq ← instantiateMVars (← mkLambdaFVars xs eq)
      return ⟨proof, eq, recVal.levelParams.toArray⟩
  return Array.mk res

/-- From a user-provided term `stx`, produce a lemma -/
def elabLemma (stx : Term) : TacticM (Array Lemma) := do
  match stx with
  | `($id:ident) =>
    let some expr ← Term.resolveId? id
      | throwError "Unknown identifier {id}"

    match (← getEnv).find? expr.constName! with
    | some (.recInfo val) => addRecAsLemma val
    | some (.defnInfo defval) =>
      let term := defval.value
      let type ← Meta.inferType term
      let sort ← Meta.reduce (← Meta.inferType type) true true false
      -- If the fact is of sort `Prop`, add itself as a fact
      let mut ret := #[]
      if sort.isProp then
        ret := ret.push (← elabLemmaAux stx)
      -- Generate definitional equation for the fact
      if let some eqns ← getEqnsFor? expr.constName! (nonRec := true) then
        ret := ret.append (← eqns.mapM fun eq => do elabLemmaAux (← `($(mkIdent eq))))
      return ret
    | some (.axiomInfo _)  => return #[← elabLemmaAux stx]
    | some (.thmInfo _)    => return #[← elabLemmaAux stx]
    | some (.opaqueInfo _) => throwError "Opaque constants cannot be provided as facts"
    | some (.quotInfo _)   => throwError "Quotient constants cannot be provided as facts"
    | some (.inductInfo _) => throwError "Inductive types cannot be provided as facts"
    | some (.ctorInfo _)   => throwError "Constructors cannot be provided as facts"
    | none => throwError "Unknown constant {expr.constName!}"
  | _ => return #[← elabLemmaAux stx]
where elabLemmaAux (stx : Term) : TacticM Lemma :=
  -- elaborate term as much as possible and abstract any remaining mvars:
  Term.withoutModifyingElabMetaStateWithInfo <| withRef stx <| Term.withoutErrToSorry do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    let abstres ← Auto.abstractMVars e
    let e := abstres.expr
    let paramNames := abstres.paramNames
    return Lemma.mk e (← inferType e) paramNames

end Prep

end Auto