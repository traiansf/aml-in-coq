From stdpp Require Import prelude.
From AML Require Import Signature Pattern Variables Substitution.
From AML.Proofs Require Import TautologicalProof ProofSystem.
From AML.Lib Require Import Ensemble.

Section sec_theorems.

Context `{signature} `{Set_ Pattern PatternSet}.

Inductive MLGammaTheorem (Gamma : PatternSet) : Pattern -> Prop :=
| ml_thm_assumption : forall ϕ, ϕ ∈ Gamma -> MLGammaTheorem Gamma ϕ
| ml_thm_tautology : forall ϕ, MLTautology ϕ -> MLGammaTheorem Gamma ϕ
| ml_thm_axiom : forall ϕ, MLAxiom ϕ -> MLGammaTheorem Gamma ϕ
| ml_thm_modus_ponens : forall ϕ ψ χ,
    MLModusPonens ϕ ψ χ ->
    MLGammaTheorem Gamma ϕ ->
    MLGammaTheorem Gamma ψ ->
    MLGammaTheorem Gamma χ
| ml_thm_single_premise : forall ϕ ψ,
    MLSinglePremiseRule ϕ ψ ->
    MLGammaTheorem Gamma ϕ ->
    MLGammaTheorem Gamma ψ
.

Definition set_deduction (Gamma Delta : PatternSet) : Prop :=
  forall ϕ, ϕ ∈ Delta -> MLGammaTheorem Gamma ϕ.

End sec_theorems.

Global Infix "⊢" := MLGammaTheorem (at level 60, no associativity).
Global Infix "⊢ₛ" := set_deduction (at level 60, no associativity).

Section sec_theorem_properties.

Context
  `{signature}
  `{Set_ Pattern PatternSet}.

Definition MLTheorem (ϕ : Pattern) : Prop :=
  MLGammaTheorem (PatternSet := PatternSet) ∅ ϕ.

Lemma gamma_theorem_subsumption :
  forall (Gamma Delta : PatternSet), Delta ⊆ Gamma ->
  forall ϕ, Delta ⊢ ϕ -> Gamma ⊢ ϕ.
Proof.
  intros * Hincl ϕ HDelta.
  induction HDelta.
  - by apply ml_thm_assumption, Hincl.
  - by apply ml_thm_tautology.
  - by apply ml_thm_axiom.
  - by eapply ml_thm_modus_ponens.
  - by eapply ml_thm_single_premise.
Qed.

Lemma theorem_subsumption :
  forall (Gamma : PatternSet) (ϕ : Pattern),
  MLTheorem ϕ -> Gamma ⊢ ϕ.
Proof.
  intro Gamma.
  apply gamma_theorem_subsumption.
  set_solver.
Qed.

Lemma set_deduction_subsumption :
  forall (Gamma Delta : PatternSet), Gamma ⊢ₛ Delta ->
  forall ϕ, Delta ⊢ ϕ -> Gamma ⊢ ϕ.
Proof.
  intros * Hincl ϕ HDelta.
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
  fun ϕ => Gamma ⊢ ϕ.

Lemma set_of_gamma_theorems_idem (Gamma : Ensemble Pattern) :
  set_of_gamma_theorems (set_of_gamma_theorems Gamma)
    ≡
  set_of_gamma_theorems Gamma.
Proof.
  intro ϕ; split.
  - by apply set_deduction_subsumption; intro.
  - apply gamma_theorem_subsumption.
    by intros ? ?; apply ml_thm_assumption.
Qed.

End sec_theorem_ensemble.
