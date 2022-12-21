From stdpp Require Import prelude.
From AML Require Import Signature.
From AML.Syntax Require Import Pattern.

Section sec_pattern_translation.

Context
  `{sign1 : signature EVar SVar Sigma1 EVarSet SVarSet}
  `{EqDecision Sigma2}
  `{sign2 : !signature EVar SVar Sigma2 EVarSet SVarSet}
  (h : Sigma1 -> Sigma2)
  `{!SignatureMorphism sign1 sign2 h}.

Fixpoint pattern_translation (p : Pattern (Sigma := Sigma1))
  : Pattern (Sigma := Sigma2) :=
  match p with
  | PEVar e => PEVar e
  | PSVar s => PSVar s
  | p1 →ₚ p2 => pattern_translation p1 →ₚ pattern_translation p2
  | PEx e p => PEx e (pattern_translation p)
  | μₚ s p => μₚ s (pattern_translation p)
  | PApp p1 p2 => PApp (pattern_translation p1) (pattern_translation p2)
  | POp s => POp (h s)
  end.

Definition pattern_set_translation
  `{FinSet (Pattern (Sigma := Sigma1)) PatternSet1}
  `{FinSet (Pattern (Sigma := Sigma2)) PatternSet2}
    (Γ : PatternSet1)
  : PatternSet2 :=
  set_map pattern_translation Γ.

End sec_pattern_translation.
