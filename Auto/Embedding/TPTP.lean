import Auto.Embedding.LamBase

namespace Auto.TPTP
open Embedding.Lam

def encodeLamBaseSort : LamBaseSort → String
| .prop => "$o"
| .int  => "$int"
| .real => "$real"
| .bv _ => panic! "No Bitvector support"

def encodeLamSort : LamSort → String
| .atom n     => s!"s{n}"
| .base b     => encodeLamBaseSort b
| .func s1 s2 => s!"({encodeLamSort s1} > {encodeLamSort s2})"

def encodeCstrReal : CstrReal → String
| .zero => "0.0"
| .one => "1.0"

def encodeLamBaseTerm : LamBaseTerm → String
| .trueE      => s!"$true"
| .falseE     => s!"$false"
| .not        => s!"(~)"
| .and        => s!"(&)"
| .or         => s!"(|)"
| .imp        => s!"(=>)"
| .iff        => s!"(=)" -- Zipperposition seems buggy on (<=>)
| .intVal n   => s!"{n}"
| .realVal cr => s!"{encodeCstrReal cr}"
| .bvVal _    => panic! "No Bitvector support"
| .eqI _      => s!"(=)"
| .forallEI _ => s!"!!"
| .existEI _  => s!"??"
| .eq _       => s!"(=)"
| .forallE _  => s!"!!"
| .existE _   => s!"??"

def encodeLamTerm (t : LamTerm) (lamDepth := 0) : String :=
  match t with
  | .atom n      => s!"a{n}"
  | .etom n      => s!"e{n}"
  | .base b      => encodeLamBaseTerm b
  | .bvar n      => s!"X{lamDepth - n}"
  | .lam s t     => s!"(^ [X{lamDepth + 1} : {encodeLamSort s}] : {encodeLamTerm t (lamDepth + 1)})"
  | .app _ t₁ t₂ => s!"({encodeLamTerm t₁ lamDepth} @ {encodeLamTerm t₂ lamDepth})"

def encodeFacts (facts : Array LamTerm) (tyVal : Array (Expr × Level)) (varVal : Array (Expr × Embedding.Lam.LamSort)) : String := Id.run do
  let sorts := tyVal.zipWithIndex.map fun (_, i) =>
    s!"thf(s{i}_type ,type, s{i}: $tType).\n"
  let types := varVal.zipWithIndex.map fun ((_, s), i) =>
    s!"thf(a{i}_type ,type, a{i}: {encodeLamSort s}).\n"
  let facts := facts.zipWithIndex.map fun (t, i) => 
    s!"thf(axiom{i},axiom,{encodeLamTerm t}).\n"
  return s!"{String.join sorts.toList}\n\n{String.join types.toList}\n\n{String.join facts.toList}"
  

#eval encodeLamTerm (.atom 0)
#eval encodeLamTerm (.lam (.atom 0) (.lam (.atom 0) (.lam (.atom 0) (.bvar 2))))
#eval encodeLamTerm $ .app (.atom 0) (.lam (.atom 0) (.bvar 0)) (.etom 0)

end Auto.TPTP