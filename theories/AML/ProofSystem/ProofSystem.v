From stdpp Require Import prelude.
From AML Require Import Signature Pattern Variables Substitution.
From AML.Lib Require Import Ensemble.

Section sec_proof_system.

Context
  `{signature}
  `{Set_ Pattern PatternSet}.

Inductive MLPropAxiom : Pattern -> Prop :=
| ax_p1 : forall phi psi,
    ClosedPattern phi ->
    ClosedPattern psi ->
    MLPropAxiom (PImpl phi (PImpl psi phi))
| ax_p2 : forall phi psi chi,
    ClosedPattern phi ->
    ClosedPattern psi ->
    ClosedPattern chi ->
    MLPropAxiom (PImpl
        (PImpl phi (PImpl psi chi))
        (PImpl (PImpl phi psi) (PImpl phi chi)))
| ax_p3 : forall phi psi,
    ClosedPattern phi ->
    ClosedPattern psi ->
    MLPropAxiom (PImpl
        (PImpl (pNeg phi) (pNeg psi))
        (PImpl psi phi))
.

Inductive MLTautology : Pattern -> Prop :=
| ml_tauto_ax : forall phi, MLPropAxiom phi -> MLTautology phi
| ml_tauto_modus_ponens : forall phi psi,
    MLTautology phi ->
    MLTautology (PImpl phi psi) ->
    MLTautology psi.

Inductive MLAxiom : Pattern -> Prop :=
| ax_ex_quantifier : forall x y phi,
    MLAxiom (PImpl (evar_sub0 x (PEVar y) phi) (PEx x phi))
| ax_propagation_bot_l : forall phi,
    MLAxiom (PImpl (PApp pBot phi) pBot)
| ax_propagation_bot_r : forall phi,
    MLAxiom (PImpl (PApp phi pBot) pBot)
| ax_propagation_or_l : forall phi psi chi,
    MLAxiom (PImpl (PApp (pOr phi psi) chi) (pOr (PApp phi chi) (PApp psi chi)))
| ax_propagation_or_r : forall phi psi chi,
    MLAxiom (PImpl (PApp chi (pOr phi psi)) (pOr (PApp chi phi) (PApp chi psi)))
| ax_propagation_ex_l : forall x phi psi,
    x ∉ FEV psi ->
    MLAxiom (PImpl (PApp (PEx x phi) psi) (PEx x (PApp phi psi)))
| ax_propagation_ex_r : forall x phi psi,
    x ∉ FEV psi ->
    MLAxiom (PImpl (PApp psi (PEx x phi)) (PEx x (PApp psi phi)))
| ax_pre_fixpoint : forall X phi,
    OccursPositively X phi ->
    SFreeFor X (PMu X phi) phi ->
    MLAxiom (PImpl (svar_sub0 X (PMu X phi) phi) (PMu X phi))
| ax_existence : forall x,
    MLAxiom (PEx x (PEVar x))
| ax_singleton_variable : forall x phi C1 C2,
    MLAxiom (pNeg (pAnd (csubst C1 (pAnd x phi)) (csubst C2 (pAnd x (pNeg phi)))))
.

Inductive MLGammaTheorem (Gamma : PatternSet) : Pattern -> Prop :=
| ml_thm_assumption : forall phi, phi ∈ Gamma -> MLGammaTheorem Gamma phi
| ml_thm_tautology : forall phi, MLTautology phi -> MLGammaTheorem Gamma phi
| ml_thm_axiom : forall phi, MLAxiom phi -> MLGammaTheorem Gamma phi
| ml_thm_modus_ponens : forall phi psi,
    MLGammaTheorem Gamma phi ->
    MLGammaTheorem Gamma (PImpl phi psi) ->
    MLGammaTheorem Gamma psi
| ml_thm_ex_quantifier_rule : forall x phi psi,
    ~ x ∈ FEV psi ->
    MLGammaTheorem Gamma (PImpl phi psi) ->
    MLGammaTheorem Gamma (PImpl (PEx x phi) psi)
| ml_thm_framing_l : forall phi psi chi,
    MLGammaTheorem Gamma (PImpl phi psi) ->
    MLGammaTheorem Gamma (PImpl (PApp phi chi) (PApp psi chi))
| ml_thm_framing_r : forall phi psi chi,
    MLGammaTheorem Gamma (PImpl phi psi) ->
    MLGammaTheorem Gamma (PImpl (PApp chi phi) (PApp chi psi))
| ml_thm_set_variable_substitution : forall phi X psi,
    SFreeFor X psi phi ->
    MLGammaTheorem Gamma phi ->
    MLGammaTheorem Gamma (svar_sub0 X psi phi)
| ml_thm_knaster_tarsky : forall phi X psi,
    SFreeFor X psi phi ->
    MLGammaTheorem Gamma (PImpl (svar_sub0 X psi phi) psi) ->
    MLGammaTheorem Gamma (PImpl (PMu X phi) psi)
.

Definition set_deduction (Gamma Delta : PatternSet) : Prop :=
  forall phi, phi ∈ Delta -> MLGammaTheorem Gamma phi.

End sec_proof_system.

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
  - by eapply ml_thm_modus_ponens; [exact IHHDelta1 |].
  - by apply ml_thm_ex_quantifier_rule.
  - by apply ml_thm_framing_l.
  - by apply ml_thm_framing_r.
  - by apply ml_thm_set_variable_substitution. 
  - by apply ml_thm_knaster_tarsky.
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
  - by eapply ml_thm_modus_ponens; [exact IHHDelta1 |].
  - by apply ml_thm_ex_quantifier_rule.
  - by apply ml_thm_framing_l.
  - by apply ml_thm_framing_r.
  - by apply ml_thm_set_variable_substitution. 
  - by apply ml_thm_knaster_tarsky.
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
