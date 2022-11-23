From stdpp Require Import prelude.
From AML Require Import Signature Pattern Variables Substitution.
From AML.Proofs Require Import TautologicalProof ProofSystem Theorems.

Section sec_proofs.

Context
  `{signature}
  `{Set_ Pattern PatternSet}
  .

Inductive MLProof (Gamma : PatternSet) : list Pattern -> Prop :=
| ml_empty_proof : MLProof Gamma []
| ml_proof_assumption :
    forall proof ϕ, MLProof Gamma proof ->
        ϕ ∈ Gamma ->
        MLProof Gamma (ϕ :: proof)
| ml_proof_tautology :
    forall proof ϕ, MLProof Gamma proof ->
        MLTautology ϕ ->
        MLProof Gamma (ϕ :: proof)
| ml_proof_axiom :
    forall proof ϕ, MLProof Gamma proof ->
        MLAxiom ϕ ->
        MLProof Gamma (ϕ :: proof)
| ml_proof_modus_ponens : forall proof ϕ ψ χ,
    MLProof Gamma proof ->
    MLModusPonens ϕ ψ χ ->
    ϕ ∈ proof ->
    ψ ∈ proof ->
    MLProof Gamma (χ :: proof)
| ml_proof_single_premise : forall proof ϕ ψ,
    MLProof Gamma proof ->
    MLSinglePremiseRule ϕ ψ ->
    ϕ ∈ proof ->
    MLProof Gamma (ψ :: proof)
.

Lemma MLProof_app (Gamma : PatternSet) (proof1 proof2 : list Pattern) :
  MLProof Gamma proof1 ->
  MLProof Gamma proof2 ->
  MLProof Gamma (proof1 ++ proof2).
Proof.
  intros Hproof1 Hproof2.
  induction Hproof1; cbn; [done |..].
  - by apply ml_proof_assumption.
  - by apply ml_proof_tautology.
  - by apply ml_proof_axiom.
  - by apply ml_proof_modus_ponens with ϕ ψ;
      [ | | apply elem_of_app; left..].
  - by apply ml_proof_single_premise with ϕ; [..| apply elem_of_app; left].
Qed.

Lemma MLProof_suffix (Gamma : PatternSet) (proof1 proof2 : list Pattern) :
  MLProof Gamma (proof1 ++ proof2) ->
  MLProof Gamma proof2.
Proof.
  induction proof1; [done |]; inversion 1; subst.
  all: by apply IHproof1.
Qed.

Lemma MLTheoremProofs_iff (Gamma : PatternSet) (ϕ : Pattern) :
  Gamma ⊢ ϕ
    <->
  exists proof, MLProof Gamma (ϕ :: proof).
Proof.
  split.
  - induction 1.
    + by exists []; apply ml_proof_assumption; [constructor |].
    + by exists []; apply ml_proof_tautology; [constructor |].
    + by exists []; apply ml_proof_axiom; [constructor |].
    + destruct IHMLGammaTheorem1 as [proof_ϕ Hproof_ϕ].
      destruct IHMLGammaTheorem2 as [proof_ψ Hproof_ψ].
      exists ((ϕ :: proof_ϕ) ++ ψ :: proof_ψ). 
      apply ml_proof_modus_ponens with ϕ ψ.
      * by apply MLProof_app.
      * done.
      * by apply elem_of_app; left; left.
      * by apply elem_of_app; right; left.
    + destruct IHMLGammaTheorem as [proof_ϕ Hproof_ϕ].
      exists (ϕ :: proof_ϕ).
      by eapply ml_proof_single_premise; [..| left].
  - intros [proof Hproof].
    remember (length (ϕ :: proof)) as n.
    revert ϕ proof Hproof Heqn.
    induction n as [n Hind] using (well_founded_ind lt_wf).
    intros; inversion Hproof
      as [| | | | ? ? ? ? Hpf Hmp Hϕ0 Hψ | ? ? ? ? Hsp Hϕ0]; subst.
    + by apply ml_thm_assumption.
    + by apply ml_thm_tautology.
    + by apply ml_thm_axiom.
    + apply elem_of_list_split in Hϕ0 as (? & proof_ϕ0 & Heqproof_ϕ0).
      assert (Hϕ0 : MLProof Gamma (ϕ0 :: proof_ϕ0))
        by (subst; eapply MLProof_suffix; done). 
      apply (f_equal length) in Heqproof_ϕ0.
      apply elem_of_list_split in Hψ as (? & proof_ψ & Heqproof_ψ).
      assert (Hψ : MLProof Gamma (ψ :: proof_ψ))
        by (subst; eapply MLProof_suffix; done). 
      apply (f_equal length) in Heqproof_ψ.
      rewrite app_length in Heqproof_ϕ0, Heqproof_ψ; cbn in Heqproof_ϕ0, Heqproof_ψ.
      apply ml_thm_modus_ponens with ϕ0 ψ; [done |..]; eapply Hind.
      2,3,5,6: done.
      all: cbn; lia.
    + apply elem_of_list_split in Hϕ0 as (? & proof_ϕ0 & Heqproof_ϕ0).
      assert (Hϕ0 : MLProof Gamma (ϕ0 :: proof_ϕ0))
        by (subst; eapply MLProof_suffix; done). 
      apply (f_equal length) in Heqproof_ϕ0.
      rewrite app_length in Heqproof_ϕ0; cbn in Heqproof_ϕ0.
      eapply ml_thm_single_premise; [done |].
      eapply Hind; [| done..].
      by cbn; lia.
Qed.



End sec_proofs.
