From stdpp Require Import prelude.
From AML Require Import Signature Pattern Variables Substitution.
From AML.Proofs Require Import ProofSystem Theorems.

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

Lemma TheoremProofs_iff (Gamma : PatternSet) (phi : Pattern) :
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
      * admit.
      * done.
      * by apply elem_of_app; left; left.
      * by apply elem_of_app; right; left.
    + destruct IHMLGammaTheorem as [proof_phi Hproof_phi].
      exists (phi :: proof_phi).
      by eapply ml_proof_single_premise; [..| left].
  - intros [proof Hproof].
    remember (phi :: proof) as proof'.
    revert phi proof Heqproof'.
    induction Hproof; inversion 1; subst phi0 proof0.
    +


End sec_proofs.
