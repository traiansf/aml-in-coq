From stdpp Require Import prelude.
From AML.Lib Require Import Ensemble.
From AML Require Import Signature.
From AML.Syntax Require Import Pattern.
From AML.Proofs Require Import ProofSystem Theorems.
From AML.Semantics Require Import StrongSemanticConsequence Validity Tautology.

Section sec_strong_soundness.

Context
  `{signature}
  `{Set_ Pattern PatternSet}
  .

Lemma strong_soundness (Γ : PatternSet) (ϕ : Pattern) :
  Γ ⊢ₛ ϕ -> Γ ⊧ₛ ϕ.
Proof.
  induction 1 as [| | ϕ Hax | |].
  - intros A e a Ha.
    unfold PatternValuation.set_pattern_valuation,
      PropositionalPatternValuation.set_propositional_pattern_valuation in Ha.
    rewrite elem_of_filtered_intersection in Ha.
    by apply Ha.
  - by apply valid_set_strong_semantic_consequence_any,
      tautology_valid.
  - inversion Hax.
    + apply valid_set_strong_semantic_consequence_any.
      by apply valid_evar_sub0_rename_ex.
Admitted.

End sec_strong_soundness.
