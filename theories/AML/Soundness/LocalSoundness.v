From stdpp Require Import prelude.
From AML.Lib Require Import Ensemble.
From AML Require Import Signature.
From AML.Syntax Require Import Pattern.
From AML.Proofs Require Import ProofSystem Theorems.
From AML.Semantics Require Import LocalSemanticConsequence.
From AML.Soundness Require Import StrongSoundness.

Section sec_local_soundness.

Context
  `{signature}
  `{Set_ Pattern PatternSet}
  .

Lemma local_soundness (Γ : PatternSet) (ϕ : Pattern) :
  Γ ⊢ₗ ϕ -> Γ ⊧ₗ ϕ.
Proof.
  induction 1 as [| | | | ? ? Hpremise].
  - apply set_strong_semantic_consequence_local, strong_soundness.
    by apply ml_thm_assumption.
  - apply set_strong_semantic_consequence_local, strong_soundness.
    by apply ml_thm_tautology.
  - apply set_strong_semantic_consequence_local, strong_soundness.
    by apply ml_thm_axiom.
  - inversion X; subst.
    by apply set_local_mp with ϕ.
  - inversion Hpremise as [| | ? ? ? Hfree Hsub].
    + by subst; apply set_local_semantic_consequence_impl_app_elim_l.
    + by subst; apply set_local_semantic_consequence_impl_app_elim_r.
    + by subst; apply set_local_semantic_consequence_knaster_tarski.
Qed.

End sec_local_soundness.
