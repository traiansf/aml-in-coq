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
    forall proof phi, MLProof Gamma proof ->
        phi ∈ Gamma ->
        MLProof Gamma (phi :: proof)
| ml_proof_tautology :
    forall proof phi, MLProof Gamma proof ->
        MLTautology phi ->
        MLProof Gamma (phi :: proof)
| ml_proof_axiom :
    forall proof phi, MLProof Gamma proof ->
        MLAxiom phi ->
        MLProof Gamma (phi :: proof)
| ml_proof_modus_ponens : forall proof phi psi chi,
    MLProof Gamma proof ->
    MLModusPonens phi psi chi ->
    phi ∈ proof ->
    psi ∈ proof ->
    MLProof Gamma (chi :: proof)
| ml_proof_single_premise : forall proof phi psi,
    MLProof Gamma proof ->
    MLSinglePremiseRule phi psi ->
    phi ∈ proof ->
    MLProof Gamma (psi :: proof)
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
  - by apply ml_proof_modus_ponens with phi psi;
      [ | | apply elem_of_app; left..].
  - by apply ml_proof_single_premise with phi; [..| apply elem_of_app; left].
Qed.

Lemma MLProof_suffix (Gamma : PatternSet) (proof1 proof2 : list Pattern) :
  MLProof Gamma (proof1 ++ proof2) ->
  MLProof Gamma proof2.
Proof.
  induction proof1; [done |]; inversion 1; subst.
  all: by apply IHproof1.
Qed.

Lemma MLTheoremProofs_iff (Gamma : PatternSet) (phi : Pattern) :
  Gamma ⊢ phi
    <->
  exists proof, MLProof Gamma (phi :: proof).
Proof.
  split.
  - induction 1.
    + by exists []; apply ml_proof_assumption; [constructor |].
    + by exists []; apply ml_proof_tautology; [constructor |].
    + by exists []; apply ml_proof_axiom; [constructor |].
    + destruct IHMLGammaTheorem1 as [proof_phi Hproof_phi].
      destruct IHMLGammaTheorem2 as [proof_psi Hproof_psi].
      exists ((phi :: proof_phi) ++ psi :: proof_psi). 
      apply ml_proof_modus_ponens with phi psi.
      * by apply MLProof_app.
      * done.
      * by apply elem_of_app; left; left.
      * by apply elem_of_app; right; left.
    + destruct IHMLGammaTheorem as [proof_phi Hproof_phi].
      exists (phi :: proof_phi).
      by eapply ml_proof_single_premise; [..| left].
  - intros [proof Hproof].
    remember (length (phi :: proof)) as n.
    revert phi proof Hproof Heqn.
    induction n as [n Hind] using (well_founded_ind lt_wf).
    intros; inversion Hproof
      as [| | | | ? ? ? ? Hpf Hmp Hphi0 Hpsi | ? ? ? ? Hsp Hphi0]; subst.
    + by apply ml_thm_assumption.
    + by apply ml_thm_tautology.
    + by apply ml_thm_axiom.
    + apply elem_of_list_split in Hphi0 as (? & proof_phi0 & Heqproof_phi0).
      assert (Hphi0 : MLProof Gamma (phi0 :: proof_phi0))
        by (subst; eapply MLProof_suffix; done). 
      apply (f_equal length) in Heqproof_phi0.
      apply elem_of_list_split in Hpsi as (? & proof_psi & Heqproof_psi).
      assert (Hpsi : MLProof Gamma (psi :: proof_psi))
        by (subst; eapply MLProof_suffix; done). 
      apply (f_equal length) in Heqproof_psi.
      rewrite app_length in Heqproof_phi0, Heqproof_psi; cbn in Heqproof_phi0, Heqproof_psi.
      apply ml_thm_modus_ponens with phi0 psi; [done |..]; eapply Hind.
      2,3,5,6: done.
      all: cbn; lia.
    + apply elem_of_list_split in Hphi0 as (? & proof_phi0 & Heqproof_phi0).
      assert (Hphi0 : MLProof Gamma (phi0 :: proof_phi0))
        by (subst; eapply MLProof_suffix; done). 
      apply (f_equal length) in Heqproof_phi0.
      rewrite app_length in Heqproof_phi0; cbn in Heqproof_phi0.
      eapply ml_thm_single_premise; [done |].
      eapply Hind; [| done..].
      by cbn; lia.
Qed.

End sec_proofs.
