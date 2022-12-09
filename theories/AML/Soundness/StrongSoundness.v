From stdpp Require Import prelude.
From AML.Lib Require Import Ensemble.
From AML Require Import Signature.
From AML.Syntax Require Import Pattern.
From AML.Proofs Require Import ProofSystem Theorems.
From AML.Semantics Require Import Validity Tautology GlobalSemanticConsequence.
From AML.Semantics Require Import StrongSemanticConsequence.

Section sec_strong_soundness.

Context
  `{signature}
  `{Set_ Pattern PatternSet}
  .

Lemma strong_soundness (Γ : PatternSet) (ϕ : Pattern) :
  Γ ⊢ₛ ϕ -> Γ ⊧ₛ ϕ.
Proof.
  induction 1 as [| | ϕ Hax | | ? ? Hpremise].
  - intros A e a Ha.
    unfold PatternValuation.set_pattern_valuation,
      PropositionalPatternValuation.set_propositional_pattern_valuation in Ha.
    rewrite elem_of_filtered_intersection in Ha.
    by apply Ha.
  - by apply valid_set_strong_semantic_consequence_any,
      tautology_valid.
  - inversion Hax as [| | | | | ? ? ? Hx | ? ? ? Hx | ? ? Hpos Hfree | |].
    + apply valid_set_strong_semantic_consequence_any.
      by apply valid_evar_sub0_rename_ex.
    + apply valid_set_strong_semantic_consequence_any.
      pose proof (Hiff := valid_iff_app_bot_l ϕ0).
      by apply valid_iff_alt_classic in Hiff as [].
    + apply valid_set_strong_semantic_consequence_any.
      pose proof (Hiff := valid_iff_app_bot_r ϕ0).
      by apply valid_iff_alt_classic in Hiff as [].
    + apply valid_set_strong_semantic_consequence_any.
      pose proof (Hiff := valid_iff_app_or_l ϕ0 ψ χ).
      by apply valid_iff_alt_classic in Hiff as [].
    + apply valid_set_strong_semantic_consequence_any.
      pose proof (Hiff := valid_iff_app_or_r ϕ0 ψ χ).
      by apply valid_iff_alt_classic in Hiff as [].
    + apply valid_set_strong_semantic_consequence_any.
      pose proof (Hiff := valid_iff_app_ex_l x ϕ0 ψ Hx).
      by apply valid_iff_alt_classic in Hiff as [].
    + apply valid_set_strong_semantic_consequence_any.
      pose proof (Hiff := valid_iff_app_ex_r x ϕ0 ψ Hx).
      by apply valid_iff_alt_classic in Hiff as [].
    + apply valid_set_strong_semantic_consequence_any.
      pose proof (Hiff := valid_iff_svar_sub0_mu X ϕ0 Hpos Hfree).
      by apply valid_iff_alt_classic in Hiff as [].
    + apply valid_set_strong_semantic_consequence_any.
      by apply valid_ex_x.
    + apply valid_set_strong_semantic_consequence_any.
      by unshelve eapply singleton_valiable_rule.
  - inversion X; subst.
    by apply set_strong_mp with ϕ.
  - by inversion Hpremise.
Qed.

End sec_strong_soundness.
