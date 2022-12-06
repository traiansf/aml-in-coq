From stdpp Require Import prelude.
From AML.Lib Require Import Ensemble.
From AML Require Import Signature Pattern Variables Substitution.
From AML.Proofs Require Import TautologicalProof ProofSystem.
From AML.Semantics Require Import Tautology.

Section sec_theorems.

Context `{signature} `{Set_ Pattern PatternSet}.

Inductive MLGammaTheorem (Gamma : PatternSet) : Pattern -> Prop :=
| ml_thm_assumption : forall ϕ, ϕ ∈ Gamma -> MLGammaTheorem Gamma ϕ
| ml_thm_tautology : forall ϕ, Tautology ϕ -> MLGammaTheorem Gamma ϕ
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

Section sec_derived_rules.

Context
  `{signature}
  `{Set_ Pattern PatternSet}
  (Γ : PatternSet).

Lemma ml_assumption ϕ : ϕ ∈ Γ -> Γ ⊢ ϕ.
Proof. by apply ml_thm_assumption. Qed.

Lemma ml_tautology ϕ : Tautology ϕ -> Γ ⊢ ϕ.
Proof. by apply ml_thm_tautology. Qed.

Lemma ml_ax_ex_quantifier (x y : EVar) (ϕ : Pattern) :
  Γ ⊢ evar_sub0 x (PEVar y) ϕ →ₚ PEx x ϕ.
Proof. by apply ml_thm_axiom, ax_ex_quantifier. Qed.

Lemma ml_propagation_bot_l (ϕ : Pattern) :
  Γ ⊢ PApp (⊥ₚ) ϕ →ₚ ⊥ₚ.
Proof. by apply ml_thm_axiom, ax_propagation_bot_l. Qed.

Lemma ml_propagation_bot_r (ϕ : Pattern) :
  Γ ⊢ PApp ϕ (⊥ₚ) →ₚ ⊥ₚ.
Proof. by apply ml_thm_axiom, ax_propagation_bot_r. Qed.

Lemma ml_propagation_or_l (ϕ ψ χ : Pattern) :
  Γ ⊢ PApp (ϕ ∨ₚ ψ) χ →ₚ PApp ϕ χ ∨ₚ PApp ψ χ.
Proof. by apply ml_thm_axiom, ax_propagation_or_l. Qed.

Lemma ml_propagation_or_r (ϕ ψ χ : Pattern) :
  Γ ⊢ PApp χ (ϕ ∨ₚ ψ) →ₚ PApp χ ϕ ∨ₚ PApp χ ψ.
Proof. by apply ml_thm_axiom, ax_propagation_or_r. Qed.

Lemma ml_propagation_ex_l x (ϕ χ : Pattern) (Hχ : x ∉ FEV χ) :
  Γ ⊢ PApp (PEx x ϕ) χ →ₚ PEx x (PApp ϕ χ).
Proof. by apply ml_thm_axiom, ax_propagation_ex_l. Qed.

Lemma ml_propagation_ex_r x (ϕ χ : Pattern) (Hχ : x ∉ FEV χ) :
  Γ ⊢ PApp χ (PEx x ϕ) →ₚ PEx x (PApp χ ϕ).
Proof. by apply ml_thm_axiom, ax_propagation_ex_r. Qed.

Lemma ml_pre_fixpoint : forall X ϕ,
  OccursPositively X ϕ ->
  SFreeFor X (μₚ X ϕ) ϕ ->
  Γ ⊢ (svar_sub0 X (μₚ X ϕ) ϕ) →ₚ (μₚ X ϕ).
Proof. by intros; apply ml_thm_axiom, ax_pre_fixpoint. Qed.

Lemma ml_existence : forall x,
  Γ ⊢ PEx x (PEVar x).
Proof. by intros; apply ml_thm_axiom, ax_existence. Qed.

Lemma ml_singleton_variable : forall x ϕ C1 C2,
  Γ ⊢ ¬ₚ (csubst C1 (x ∧ₚ ϕ) ∧ₚ csubst C2 (x ∧ₚ ¬ₚ ϕ)).
Proof. by intros; apply ml_thm_axiom, ax_singleton_variable. Qed.

Lemma ml_ex_quantifier : forall x ϕ ψ,
  ~ x ∈ FEV ψ ->
  Γ ⊢ ϕ →ₚ ψ ->
  Γ ⊢ PEx x ϕ →ₚ ψ.
Proof. by intros; eapply ml_thm_single_premise; [apply rule_ex_quantifier |]. Qed.

Lemma ml_framing_l : forall ϕ ψ χ,
  Γ ⊢ ϕ →ₚ ψ ->
  Γ ⊢ PApp ϕ χ →ₚ PApp ψ χ.
Proof. by intros; eapply ml_thm_single_premise; [apply rule_framing_l |]. Qed.

Lemma ml_framing_r : forall ϕ ψ χ,
  Γ ⊢ ϕ →ₚ ψ ->
  Γ ⊢ PApp χ ϕ →ₚ PApp χ ψ.
Proof. by intros; eapply ml_thm_single_premise; [apply rule_framing_r |]. Qed.

Lemma ml_set_variable_substitution : forall ϕ X ψ,
    SFreeFor X ψ ϕ ->
    Γ ⊢ ϕ ->
    Γ ⊢ svar_sub0 X ψ ϕ.
Proof.
  by intros; eapply ml_thm_single_premise; [apply rule_set_variable_substitution |].
Qed.

Lemma ml_knaster_tarsky : forall ϕ X ψ,
    SFreeFor X ψ ϕ ->
    Γ ⊢ svar_sub0 X ψ ϕ →ₚ ψ ->
    Γ ⊢ μₚ X ϕ →ₚ ψ.
Proof.
  by intros; eapply ml_thm_single_premise; [apply rule_knaster_tarsky |].
Qed.

Lemma ml_modus_ponens : forall ϕ ψ,
  Γ ⊢ ϕ ->
  Γ ⊢ ϕ →ₚ ψ ->
  Γ ⊢ ψ.
Proof. by intros ? ?; eapply ml_thm_modus_ponens. Qed.

Lemma ml_equivalent_goal ϕ ψ :
  Tautology (ϕ ↔ₚ ψ) ->
  Γ ⊢ ϕ ->
  Γ ⊢ ψ.
Proof.
  intros.
  eapply ml_modus_ponens; [done |].
  eapply ml_modus_ponens; [by apply ml_tautology |].
  by apply ml_tautology, tautology_ϕ_and_ψ_impl_ϕ.
Qed.

End sec_derived_rules.
