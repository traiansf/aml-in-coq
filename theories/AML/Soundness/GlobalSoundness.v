From stdpp Require Import prelude.
From AML.Lib Require Import Ensemble.
From AML Require Import Signature.
From AML.Syntax Require Import Pattern.
From AML.Proofs Require Import ProofSystem Theorems.
From AML.Semantics Require Import GlobalSemanticConsequence.
From AML.Soundness Require Import LocalSoundness.

Section sec_global_soundness.

Context
  `{signature}
  `{Set_ Pattern PatternSet}
  .

Lemma global_soundness (Γ : PatternSet) (ϕ : Pattern) :
  Γ ⊢ ϕ -> Γ ⊧ ϕ.
Proof.
  induction 1 as [| | | | ? ? Hpremise].
  - apply set_local_semantic_consequence_global, local_soundness.
    by apply ml_thm_assumption.
  - apply set_local_semantic_consequence_global, local_soundness.
    by apply ml_thm_tautology.
  - apply set_local_semantic_consequence_global, local_soundness.
    by apply ml_thm_axiom.
  - inversion X; subst.
    by apply set_global_mp with ϕ.
  - inversion Hpremise as [? ? Hsingle| | ]; subst.
    + inversion Hsingle as [| | ? ? ? Hfree Hsub].
      * by subst; apply set_global_semantic_consequence_impl_app_elim_l.
      * by subst; apply set_global_semantic_consequence_impl_app_elim_r.
      * by subst; apply set_global_semantic_consequence_knaster_tarski.
    + by apply set_global_impl_ex_elim.
    + by apply set_global_semantic_consequence_svar_sub0.
Qed.

End sec_global_soundness.
