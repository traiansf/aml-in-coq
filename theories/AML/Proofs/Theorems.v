From stdpp Require Import prelude.
From AML Require Import Signature Pattern Variables Substitution.
From AML.Proofs Require Import TautologicalProof ProofSystem.
From AML.Lib Require Import Ensemble.

Section sec_theorems.

Context `{signature} `{Set_ Pattern PatternSet}.


Inductive MLGammaTheorem (Gamma : PatternSet) : Pattern -> Prop :=
| ml_thm_assumption : forall phi, phi ∈ Gamma -> MLGammaTheorem Gamma phi
| ml_thm_tautology : forall phi, MLTautology phi -> MLGammaTheorem Gamma phi
| ml_thm_axiom : forall phi, MLAxiom phi -> MLGammaTheorem Gamma phi
| ml_thm_modus_ponens : forall phi psi chi,
    MLModusPonens phi psi chi ->
    MLGammaTheorem Gamma phi ->
    MLGammaTheorem Gamma psi ->
    MLGammaTheorem Gamma chi
| ml_thm_single_premise : forall phi psi,
    MLSinglePremiseRule phi psi ->
    MLGammaTheorem Gamma phi ->
    MLGammaTheorem Gamma psi
.

Definition set_deduction (Gamma Delta : PatternSet) : Prop :=
  forall phi, phi ∈ Delta -> MLGammaTheorem Gamma phi.

End sec_theorems.

Global Infix "⊢" := MLGammaTheorem (at level 60, no associativity).
Global Infix "⊢ₛ" := set_deduction (at level 60, no associativity).

Section sec_theorem_properties.

Context
  `{signature}
  `{Set_ Pattern PatternSet}.

Definition MLTheorem (phi : Pattern) : Prop :=
  MLGammaTheorem (PatternSet := PatternSet) ∅ phi.

Lemma gamma_theorem_subsumption :
  forall (Gamma Delta : PatternSet), Delta ⊆ Gamma ->
  forall phi, Delta ⊢ phi -> Gamma ⊢ phi.
Proof.
  intros * Hincl phi HDelta.
  induction HDelta.
  - by apply ml_thm_assumption, Hincl.
  - by apply ml_thm_tautology.
  - by apply ml_thm_axiom.
  - by eapply ml_thm_modus_ponens.
  - by eapply ml_thm_single_premise.
Qed.

Lemma theorem_subsumption :
  forall (Gamma : PatternSet) (phi : Pattern),
  MLTheorem phi -> Gamma ⊢ phi.
Proof.
  intro Gamma.
  apply gamma_theorem_subsumption.
  set_solver.
Qed.

Lemma set_deduction_subsumption :
  forall (Gamma Delta : PatternSet), Gamma ⊢ₛ Delta ->
  forall phi, Delta ⊢ phi -> Gamma ⊢ phi.
Proof.
  intros * Hincl phi HDelta.
  induction HDelta.
  - by apply Hincl.
  - by apply ml_thm_tautology.
  - by apply ml_thm_axiom.
  - by eapply ml_thm_modus_ponens.
  - by eapply ml_thm_single_premise.
Qed.

End sec_theorem_properties.

Section sec_theorem_ensemble.

Context `{signature}.

Definition set_of_gamma_theorems (Gamma : Ensemble Pattern) : Ensemble Pattern :=
  fun phi => Gamma ⊢ phi.

Lemma set_of_gamma_theorems_idem (Gamma : Ensemble Pattern) :
  set_of_gamma_theorems (set_of_gamma_theorems Gamma)
    ≡
  set_of_gamma_theorems Gamma.
Proof.
  intro phi; split.
  - by apply set_deduction_subsumption; intro.
  - apply gamma_theorem_subsumption.
    by intros ? ?; apply ml_thm_assumption.
Qed.

End sec_theorem_ensemble.
