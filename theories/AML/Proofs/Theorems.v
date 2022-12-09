From stdpp Require Import prelude.
From AML.Lib Require Import Ensemble.
From AML Require Import Signature Pattern Variables Substitution.
From AML.Proofs Require Import TautologicalProof ProofSystem.
From AML.Semantics Require Import Tautology.

Section sec_theorems.

Context
  `{signature}
  `{Set_ Pattern PatternSet}
  .

Section sec_parameterized_definition.

Context (single_premise_rule : Pattern -> Pattern -> Prop).

Inductive MLXGammaTheorem (Gamma : PatternSet) : Pattern -> Prop :=
| ml_thm_assumption : forall ϕ, ϕ ∈ Gamma -> MLXGammaTheorem Gamma ϕ
| ml_thm_tautology : forall ϕ, Tautology ϕ -> MLXGammaTheorem Gamma ϕ
| ml_thm_axiom : forall ϕ, MLAxiom ϕ -> MLXGammaTheorem Gamma ϕ
| ml_thm_modus_ponens : forall ϕ ψ χ,
    MLModusPonens ϕ ψ χ ->
    MLXGammaTheorem Gamma ϕ ->
    MLXGammaTheorem Gamma ψ ->
    MLXGammaTheorem Gamma χ
| ml_thm_single_premise : forall ϕ ψ,
    single_premise_rule ϕ ψ ->
    MLXGammaTheorem Gamma ϕ ->
    MLXGammaTheorem Gamma ψ
.

Definition x_set_deduction (Gamma Delta : PatternSet) : Prop :=
  forall ϕ, ϕ ∈ Delta -> MLXGammaTheorem Gamma ϕ.

End sec_parameterized_definition.

Definition MLStrongGammaTheorem := MLXGammaTheorem MLStrongSinglePremiseRule.
Definition MLLocalGammaTheorem := MLXGammaTheorem MLLocalSinglePremiseRule.
Definition MLGammaTheorem := MLXGammaTheorem MLGlobalSinglePremiseRule.
Definition strong_set_deduction := x_set_deduction MLStrongSinglePremiseRule.
Definition local_set_deduction := x_set_deduction MLLocalSinglePremiseRule.
Definition set_deduction := x_set_deduction MLGlobalSinglePremiseRule.

End sec_theorems.

Notation "Gamma ⊢[ spr ] phi " := (MLXGammaTheorem spr Gamma phi) (at level 60, no associativity).
Notation "Gamma |-[ spr ] Delta " := (x_set_deduction spr Gamma Delta) (at level 60, no associativity).

Infix "⊢ₛ" := MLStrongGammaTheorem (at level 60, no associativity) : ml_scope.
Infix "|-ₛ" := strong_set_deduction (at level 60, no associativity) : ml_scope.

Infix "⊢ₗ" := MLLocalGammaTheorem (at level 60, no associativity) : ml_scope.
Infix "|-ₗ" := local_set_deduction (at level 60, no associativity) : ml_scope.

Infix "⊢" := MLGammaTheorem (at level 60, no associativity) : ml_scope.
Infix "|-" := set_deduction (at level 60, no associativity) : ml_scope.

Section sec_theorem_properties.

Context
  `{signature}
  `{Set_ Pattern PatternSet}
  (single_premise_rule : Pattern -> Pattern -> Prop).

Definition MLXTheorem spr (ϕ : Pattern) : Prop :=
  MLXGammaTheorem (PatternSet := PatternSet) spr ∅ ϕ.
Definition MLTheorem := MLXTheorem MLGlobalSinglePremiseRule.
Definition MLLocalTheorem := MLXTheorem MLLocalSinglePremiseRule.
Definition MLStrongTheorem := MLXTheorem MLStrongSinglePremiseRule.

Lemma x_gamma_theorem_subsumption spr :
  forall (Gamma Delta : PatternSet), Delta ⊆ Gamma ->
  forall ϕ, Delta ⊢[spr] ϕ -> Gamma ⊢[spr] ϕ.
Proof.
  intros * Hincl ϕ HDelta.
  induction HDelta.
  - by apply ml_thm_assumption, Hincl.
  - by apply ml_thm_tautology.
  - by apply ml_thm_axiom.
  - by eapply ml_thm_modus_ponens.
  - by eapply ml_thm_single_premise.
Qed.

Definition gamma_theorem_subsumption := x_gamma_theorem_subsumption MLGlobalSinglePremiseRule.
Definition local_gamma_theorem_subsumption := x_gamma_theorem_subsumption MLLocalSinglePremiseRule.
Definition strong_gamma_theorem_subsumption := x_gamma_theorem_subsumption MLStrongSinglePremiseRule.

Lemma strong_local_deduction_subsumption (Γ : PatternSet) ϕ :
  Γ ⊢ₛ ϕ -> Γ ⊢ₗ ϕ.
Proof.
  induction 1 as [| | | | ? ? Hspr].
  - by apply ml_thm_assumption.
  - by apply ml_thm_tautology.
  - by apply ml_thm_axiom.
  - by eapply ml_thm_modus_ponens.
  - by inversion Hspr.
Qed.

Lemma strong_local_set_deduction_subsumption (Γ Δ : PatternSet) :
  Γ |-ₛ Δ -> Γ |-ₗ Δ.
Proof. by intros Hincl ϕ Hϕ; apply strong_local_deduction_subsumption, Hincl. Qed.

Lemma local_deduction_subsumption (Γ : PatternSet) ϕ :
  Γ ⊢ₗ ϕ -> Γ ⊢ ϕ.
Proof.
  induction 1 as [| | | | ? ? Hspr].
  - by apply ml_thm_assumption.
  - by apply ml_thm_tautology.
  - by apply ml_thm_axiom.
  - by eapply ml_thm_modus_ponens.
  - by eapply ml_thm_single_premise; [apply rule_local_premise |].
Qed.

Lemma local_set_deduction_subsumption (Γ Δ : PatternSet) :
  Γ |-ₗ Δ -> Γ |- Δ.
Proof. by intros Hincl ϕ Hϕ; apply local_deduction_subsumption, Hincl. Qed.

Lemma strong_deduction_subsumption (Γ : PatternSet) ϕ :
  Γ ⊢ₛ ϕ -> Γ ⊢ ϕ.
Proof. by intro; apply local_deduction_subsumption, strong_local_deduction_subsumption. Qed.

Lemma strong_set_deduction_subsumption (Γ Δ : PatternSet) :
  Γ |-ₛ Δ -> Γ |- Δ.
Proof. by intros Hincl ϕ Hϕ; apply strong_deduction_subsumption, Hincl. Qed.

Lemma x_theorem_subsumption spr :
  forall (Gamma : PatternSet) (ϕ : Pattern),
  MLXTheorem spr ϕ -> Gamma ⊢[spr] ϕ.
Proof. by intro Gamma; apply x_gamma_theorem_subsumption; set_solver. Qed.

Definition theorem_subsumption := x_theorem_subsumption MLGlobalSinglePremiseRule.
Definition local_theorem_subsumption := x_theorem_subsumption MLLocalSinglePremiseRule.
Definition strong_theorem_subsumption := x_theorem_subsumption MLStrongSinglePremiseRule.

Lemma x_set_deduction_premises_subsumption spr :
  forall (Gamma Delta : PatternSet), Gamma |-[spr] Delta ->
  forall ϕ, Delta ⊢[spr] ϕ -> Gamma ⊢[spr] ϕ.
Proof.
  intros * Hincl ϕ HDelta.
  induction HDelta.
  - by apply Hincl.
  - by apply ml_thm_tautology.
  - by apply ml_thm_axiom.
  - by eapply ml_thm_modus_ponens.
  - by eapply ml_thm_single_premise.
Qed.

Definition set_deduction_premises_subsumption := x_set_deduction_premises_subsumption MLGlobalSinglePremiseRule.
Definition local_set_deduction_premises_subsumption := x_set_deduction_premises_subsumption MLLocalSinglePremiseRule.
Definition strong_set_deduction_premises_subsumption := x_set_deduction_premises_subsumption MLStrongSinglePremiseRule.

End sec_theorem_properties.

Section sec_theorem_ensemble.

Context `{signature}.

Definition x_set_of_gamma_theorems spr (Gamma : Ensemble Pattern) : Ensemble Pattern :=
  fun ϕ => Gamma ⊢[spr] ϕ.

Lemma x_set_of_gamma_theorems_idem spr (Gamma : Ensemble Pattern) :
  x_set_of_gamma_theorems spr (x_set_of_gamma_theorems spr Gamma)
    ≡
  x_set_of_gamma_theorems spr Gamma.
Proof.
  intro ϕ; split.
  - by apply x_set_deduction_premises_subsumption; intro.
  - apply x_gamma_theorem_subsumption.
    by intros ? ?; apply ml_thm_assumption.
Qed.

End sec_theorem_ensemble.

Section sec_derived_rules.

Context
  `{signature}
  `{Set_ Pattern PatternSet}
  (Γ : PatternSet).

Lemma ml_assumption spr ϕ : ϕ ∈ Γ -> Γ ⊢[spr] ϕ.
Proof. by apply ml_thm_assumption. Qed.

Lemma ml_tautology spr ϕ : Tautology ϕ -> Γ ⊢[spr] ϕ.
Proof. by apply ml_thm_tautology. Qed.

Lemma ml_ax_ex_quantifier spr (x y : EVar) (ϕ : Pattern) :
  EFreeFor x (PEVar y) ϕ ->
  Γ ⊢[spr] evar_sub0 x (PEVar y) ϕ →ₚ PEx x ϕ.
Proof. by intros; apply ml_thm_axiom, ax_ex_quantifier. Qed.

Lemma ml_propagation_bot_l spr (ϕ : Pattern) :
  Γ ⊢[spr] PApp (⊥ₚ) ϕ →ₚ ⊥ₚ.
Proof. by apply ml_thm_axiom, ax_propagation_bot_l. Qed.

Lemma ml_propagation_bot_r spr (ϕ : Pattern) :
  Γ ⊢[spr] PApp ϕ (⊥ₚ) →ₚ ⊥ₚ.
Proof. by apply ml_thm_axiom, ax_propagation_bot_r. Qed.

Lemma ml_propagation_or_l spr (ϕ ψ χ : Pattern) :
  Γ ⊢[spr] PApp (ϕ ∨ₚ ψ) χ →ₚ PApp ϕ χ ∨ₚ PApp ψ χ.
Proof. by apply ml_thm_axiom, ax_propagation_or_l. Qed.

Lemma ml_propagation_or_r spr (ϕ ψ χ : Pattern) :
  Γ ⊢[spr] PApp χ (ϕ ∨ₚ ψ) →ₚ PApp χ ϕ ∨ₚ PApp χ ψ.
Proof. by apply ml_thm_axiom, ax_propagation_or_r. Qed.

Lemma ml_propagation_ex_l spr x (ϕ χ : Pattern) (Hχ : x ∉ FEV χ) :
  Γ ⊢[spr] PApp (PEx x ϕ) χ →ₚ PEx x (PApp ϕ χ).
Proof. by apply ml_thm_axiom, ax_propagation_ex_l. Qed.

Lemma ml_propagation_ex_r spr x (ϕ χ : Pattern) (Hχ : x ∉ FEV χ) :
  Γ ⊢[spr] PApp χ (PEx x ϕ) →ₚ PEx x (PApp χ ϕ).
Proof. by apply ml_thm_axiom, ax_propagation_ex_r. Qed.

Lemma ml_pre_fixpoint spr : forall X ϕ,
  OccursPositively X ϕ ->
  SFreeFor X (μₚ X ϕ) ϕ ->
  Γ ⊢[spr] (svar_sub0 X (μₚ X ϕ) ϕ) →ₚ (μₚ X ϕ).
Proof. by intros; apply ml_thm_axiom, ax_pre_fixpoint. Qed.

Lemma ml_existence spr : forall x,
  Γ ⊢[spr] PEx x (PEVar x).
Proof. by intros; apply ml_thm_axiom, ax_existence. Qed.

Lemma ml_singleton_variable spr : forall x ϕ C1 C2,
  Γ ⊢[spr] ¬ₚ (csubst C1 (PEVar x ∧ₚ ϕ) ∧ₚ csubst C2 (PEVar x ∧ₚ ¬ₚ ϕ)).
Proof. by intros; apply ml_thm_axiom, ax_singleton_variable. Qed.

Lemma ml_ex_quantifier : forall x ϕ ψ,
  ~ x ∈ FEV ψ ->
  Γ ⊢ ϕ →ₚ ψ ->
  Γ ⊢ PEx x ϕ →ₚ ψ.
Proof. by intros; eapply ml_thm_single_premise; [apply rule_ex_quantifier |]. Qed.

Lemma local_ml_framing_l : forall ϕ ψ χ,
  Γ ⊢ₗ ϕ →ₚ ψ ->
  Γ ⊢ₗ PApp ϕ χ →ₚ PApp ψ χ.
Proof.
  by intros; eapply ml_thm_single_premise; [apply rule_framing_l |].
Qed.

Lemma ml_framing_l : forall ϕ ψ χ,
  Γ ⊢ ϕ →ₚ ψ ->
  Γ ⊢ PApp ϕ χ →ₚ PApp ψ χ.
Proof.
  by intros; eapply ml_thm_single_premise;
    [apply rule_local_premise, rule_framing_l |].
Qed.

Lemma local_ml_framing_r : forall ϕ ψ χ,
  Γ ⊢ₗ ϕ →ₚ ψ ->
  Γ ⊢ₗ PApp χ ϕ →ₚ PApp χ ψ.
Proof.
  by intros; eapply ml_thm_single_premise; [apply rule_framing_r |].
Qed.

Lemma ml_framing_r : forall ϕ ψ χ,
  Γ ⊢ ϕ →ₚ ψ ->
  Γ ⊢ PApp χ ϕ →ₚ PApp χ ψ.
Proof.
  by intros; eapply ml_thm_single_premise;
    [apply rule_local_premise, rule_framing_r |].
Qed.

Lemma ml_set_variable_substitution : forall ϕ X ψ,
    SFreeFor X ψ ϕ ->
    Γ ⊢ ϕ ->
    Γ ⊢ svar_sub0 X ψ ϕ.
Proof.
  by intros; eapply ml_thm_single_premise; [apply rule_set_variable_substitution |].
Qed.

Lemma local_ml_knaster_tarsky : forall ϕ X ψ,
    SFreeFor X ψ ϕ ->
    Γ ⊢ₗ svar_sub0 X ψ ϕ →ₚ ψ ->
    Γ ⊢ₗ μₚ X ϕ →ₚ ψ.
Proof.
  by intros; eapply ml_thm_single_premise; [apply rule_knaster_tarsky |].
Qed.

Lemma ml_knaster_tarsky : forall ϕ X ψ,
    SFreeFor X ψ ϕ ->
    Γ ⊢ svar_sub0 X ψ ϕ →ₚ ψ ->
    Γ ⊢ μₚ X ϕ →ₚ ψ.
Proof.
  by intros; eapply ml_thm_single_premise;
    [apply rule_local_premise, rule_knaster_tarsky |].
Qed.

Lemma ml_modus_ponens spr : forall ϕ ψ,
  Γ ⊢[spr] ϕ ->
  Γ ⊢[spr] ϕ →ₚ ψ ->
  Γ ⊢[spr] ψ.
Proof. by intros ? ?; eapply ml_thm_modus_ponens. Qed.

Lemma ml_equivalent_goal spr ϕ ψ :
  Tautology (ϕ ↔ₚ ψ) ->
  Γ ⊢[spr] ϕ ->
  Γ ⊢[spr] ψ.
Proof.
  intros.
  eapply ml_modus_ponens; [done |].
  eapply ml_modus_ponens; [by apply ml_tautology |].
  by apply ml_tautology, tautology_ϕ_and_ψ_impl_ϕ.
Qed.

End sec_derived_rules.
