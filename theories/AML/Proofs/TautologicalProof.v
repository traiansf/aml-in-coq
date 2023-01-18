From stdpp Require Import prelude.
From sets Require Import List.
From AML Require Import Signature Pattern Variables Substitution.

Section sec_tautology.

Context `{signature}.

Inductive MLPropAxiom : Pattern -> Type :=
| ax_p1 : forall ϕ ψ,
    MLPropAxiom (PImpl ϕ (PImpl ψ ϕ))
| ax_p2 : forall ϕ ψ χ,
    MLPropAxiom (PImpl
        (PImpl ϕ (PImpl ψ χ))
        (PImpl (PImpl ϕ ψ) (PImpl ϕ χ)))
| ax_p3 : forall ϕ ψ,
    MLPropAxiom (PImpl
        (PImpl (pNeg ϕ) (pNeg ψ))
        (PImpl ψ ϕ))
.

Inductive MLModusPonens : Pattern -> Pattern -> Pattern -> Type :=
| rule_modus_ponens : forall ϕ ψ,
    MLModusPonens ϕ (PImpl ϕ ψ) ψ.

Inductive MLTautology : Pattern -> Type :=
| ml_tauto_axiom : forall ϕ, MLPropAxiom ϕ -> MLTautology ϕ
| ml_tauto_modus_ponens : forall ϕ ψ χ,
  MLTautology ϕ -> MLTautology ψ ->
  MLModusPonens ϕ ψ χ ->
  MLTautology χ.

End sec_tautology.

Section sec_tautologies.

Context `{signature}.

Definition tautology_impl := fun x y => MLTautology (PImpl x y).
Definition tautology_iff := fun x y => MLTautology (pIff x y).

Notation "⊢ₜ x" := (MLTautology x) (at level 60).
Notation "x ↔ₜ y" := (MLTautology (pIff x y)) (at level 60, no associativity).
Notation "x →ₜ y" := (MLTautology (PImpl x y)) (at level 60, no associativity).

Lemma ml_tautology_a1 ϕ ψ : ϕ →ₜ ψ →ₚ ϕ.
Proof. by apply ml_tauto_axiom, ax_p1. Defined.

Lemma ml_tautology_a2 ϕ ψ χ :
  ϕ →ₚ ψ →ₚ χ  →ₜ  (ϕ →ₚ ψ) →ₚ (ϕ →ₚ χ).
Proof. by apply ml_tauto_axiom, ax_p2. Defined.

Lemma ml_tautology_a3 ϕ ψ : ¬ₚ ϕ →ₚ ¬ₚ ψ  →ₜ  ψ →ₚ ϕ.
Proof. by apply ml_tauto_axiom, ax_p3. Defined.

Lemma ml_tautology_mp ϕ ψ :
  ⊢ₜ ϕ ->
  ϕ →ₜ ψ ->
  ⊢ₜ ψ.
Proof.
  by intros; eapply ml_tauto_modus_ponens; [..| constructor]; cycle 1.
Defined.

Lemma ml_tautology_a1i ϕ τ :
  ⊢ₜ τ ->
  ϕ →ₜ τ.
Proof. by intro Hp; eapply ml_tautology_mp, ml_tautology_a1. Defined.

Lemma ml_tautology_a2i ϕ ψ χ :
  ϕ →ₜ ψ →ₚ χ ->
  ϕ →ₚ ψ →ₜ ϕ →ₚ χ.
Proof. by intro Hp; eapply ml_tautology_mp, ml_tautology_a2. Defined.

Lemma ml_tautology_a3i ϕ ψ :
  ¬ₚ ϕ →ₜ ¬ₚ ψ ->
  ψ →ₜ ϕ.
Proof. by intro Hp; eapply ml_tautology_mp, ml_tautology_a3. Defined.

Lemma ml_tautology_mpd ϕ ψ χ :
  ϕ →ₜ ψ ->
  ϕ →ₜ ψ →ₚ χ ->
  ϕ →ₜ χ.
Proof.
  by intros Hψ Hchi; eapply ml_tautology_mp, ml_tautology_a2i, Hchi.
Defined.

Lemma ml_tautology_id ϕ : ϕ →ₜ ϕ.
Proof.
  by apply ml_tautology_mpd with (ϕ →ₚ ϕ); apply ml_tauto_axiom, ax_p1.
Defined.

Lemma ml_tautology_top : ⊢ₜ ⊤ₚ.
Proof. by apply ml_tautology_id. Defined.

Lemma ml_tautology_excluded_middle ϕ :
  ⊢ₜ ϕ ∨ₚ ¬ₚ ϕ.
Proof. by apply ml_tautology_id. Defined.

Lemma ml_tautology_neg_neg ϕ :
  ⊢ₜ ϕ ->
  ⊢ₜ ¬ₚ ¬ₚ ϕ.
Proof.
  intros Hϕ.
  eapply ml_tautology_mpd, ml_tautology_id.
  by apply ml_tautology_a1i.
Defined.

Lemma ml_tautology_ϕ_impl_top ϕ :
  ϕ →ₜ ⊤ₚ.
Proof. by eapply ml_tautology_a1i, ml_tautology_top. Defined.

Lemma ml_tautology_neg_tauto_impl_ϕ τ ϕ :
  ⊢ₜ τ ->
  ¬ₚ τ →ₜ ϕ.
Proof.
  by intro Hp; apply ml_tautology_a3i,
    ml_tautology_a1i, ml_tautology_neg_neg.
Defined.

Lemma ml_tautology_bot_impl ϕ : ⊥ₚ →ₜ ϕ.
Proof.
  by apply ml_tautology_a3i, ml_tautology_ϕ_impl_top.
Defined.

Lemma ml_tautology_syl ϕ ψ χ :
  ϕ →ₜ ψ -> ψ →ₜ χ -> ϕ →ₜ χ.
Proof. by intros; eapply ml_tautology_mpd, ml_tautology_a1i. Defined.

Lemma ml_tautology_or_intro_r ϕ ψ :
  ⊢ₜ ψ ->
  ⊢ₜ ϕ ∨ₚ ψ.
Proof. by intro; apply ml_tautology_a1i. Defined.

Lemma ml_tautology_or_intro_l ϕ ψ :
  ⊢ₜ ϕ ->
  ⊢ₜ ϕ ∨ₚ ψ.
Proof.
  by intro; apply ml_tautology_a3i, ml_tautology_a1i, ml_tautology_neg_neg.
Defined.

Lemma ml_tautology_a1d ϕ ψ χ :
  ϕ →ₜ ψ ->
  ϕ →ₜ χ →ₚ ψ.
Proof. by intros; eapply ml_tautology_syl, ml_tauto_axiom, ax_p1. Defined.

Lemma ml_tautology_con4d ϕ ψ χ :
  χ →ₜ ¬ₚ ϕ →ₚ ¬ₚ ψ ->
  χ →ₜ ψ →ₚ ϕ.
Proof. by intros; eapply ml_tautology_syl, ml_tauto_axiom, ax_p3. Defined.

Lemma ml_tautolology_impl_contradiction ϕ χ :
  ⊢ₜ ¬ₚ ϕ ->
  ϕ →ₜ χ.
Proof. by intro; eapply ml_tautology_a3i, ml_tautology_a1i. Defined.

Lemma ml_tautology_mp_nested ϕ ψ χ :
  ⊢ₜ ψ ->
  ϕ →ₜ ψ →ₚ χ ->
  ϕ →ₜ χ.
Proof. by intro; apply ml_tautology_mpd, ml_tautology_a1i. Defined.

Lemma ml_tautology_imim2i ϕ ψ χ :
  ϕ →ₜ ψ ->
  χ →ₚ ϕ →ₜ χ →ₚ ψ.
Proof. by intro; apply ml_tautology_a2i, ml_tautology_a1i. Defined.

Lemma ml_tautology_idd ϕ ψ : ϕ →ₜ ψ →ₚ ψ.
Proof. by apply ml_tautology_a1i, ml_tautology_id. Defined.

Lemma ml_tautology_impi ϕ ψ χ :
  ϕ →ₜ ψ →ₚ χ -> ¬ₚ(ϕ →ₚ ¬ₚψ) →ₜ χ.
Admitted.

Lemma ml_tautology_sim' ϕ ψ : ¬ₚ (ϕ →ₚ ¬ₚ ψ) →ₜ ψ.
Admitted.

Lemma ml_tautology_iff_ϕ ϕ : ϕ ↔ₜ ϕ.
Admitted.
Lemma tautology_ϕ_or_ϕ_iff_ϕ ϕ : ϕ ∨ₚ ϕ ↔ₜ ϕ. Admitted.
Lemma tautology_ϕ_iff_ϕ_and_ϕ ϕ : ϕ ↔ₜ ϕ ∧ₚ ϕ. Admitted.
Lemma tautology_or_comm ϕ ψ : ϕ ∨ₚ ψ ↔ₜ ψ ∨ₚ ϕ. Admitted.
Lemma tautology_and_comm ϕ ψ : ϕ ∧ₚ ψ ↔ₜ ψ ∧ₚ ϕ. Admitted.
Lemma tautology_ϕ_impl_ϕ_or_ψ ϕ ψ : ϕ →ₜ ϕ ∨ₚ ψ. Admitted.
Lemma tautology_ϕ_and_ψ_impl_ϕ ϕ ψ : ϕ ∧ₚ ψ →ₜ ϕ. Admitted.
Lemma tautology_impl_impl_and ϕ ψ χ : ϕ →ₚ ψ →ₚ χ ↔ₜ ϕ ∧ₚ ψ →ₚ χ. Admitted.
Lemma tautology_impl_impl_comm ϕ ψ χ : ϕ →ₚ ψ →ₚ χ ↔ₜ ψ →ₚ ϕ →ₚ χ. Admitted.

End sec_tautologies.

Section sec_basic_tautological_proof.

Context `{signature}.

Inductive MLTautologicalProof : list Pattern -> Type :=
| ml_tauto_proof_empty : MLTautologicalProof []
| ml_tauto_proof_axiom : forall ϕ proof,
    MLPropAxiom ϕ ->
    MLTautologicalProof proof ->
    MLTautologicalProof (ϕ :: proof)
| ml_tauto_proof_modus_ponens : forall ϕ ψ χ proof,
    MLModusPonens ϕ ψ χ ->
    MLTautologicalProof proof ->
    ϕ ∈ proof ->
    ψ ∈ proof ->
    MLTautologicalProof (χ :: proof).

Lemma MLTautologicalProof_app (proof1 proof2 : list Pattern) :
  MLTautologicalProof proof1 ->
  MLTautologicalProof proof2 ->
  MLTautologicalProof (proof1 ++ proof2).
Proof.
  intros Hproof1 Hproof2.
  induction Hproof1; cbn; [done |..].
  - by apply ml_tauto_proof_axiom.
  - by apply ml_tauto_proof_modus_ponens with ϕ ψ;
      [ | | apply elem_of_app; left..].
Qed.

Lemma MLTautologicalProof_suffix (proof proof1 proof2 : list Pattern) :
  proof = proof1 ++ proof2 ->
  MLTautologicalProof proof ->
  MLTautologicalProof proof2.
Proof.
  intros ->; induction proof1; [done |]; inversion 1; subst.
  all: by apply IHproof1.
Qed.

Definition ml_tautology_to_proof [ϕ : Pattern] (Hϕ :  MLTautology ϕ)
  : list Pattern.
Proof.
  induction Hϕ.
  + exact [].
  + exact ((ϕ :: IHHϕ1) ++ ψ :: IHHϕ2).
Defined.

Lemma ml_tautology_to_proof_sound (ϕ : Pattern) (Hϕ :  MLTautology ϕ) :
  MLTautologicalProof (ϕ :: ml_tautology_to_proof Hϕ).
Proof.
  induction Hϕ.
  + by apply ml_tauto_proof_axiom; [| constructor].
  + apply ml_tauto_proof_modus_ponens with ϕ ψ.
    * done.
    * by apply MLTautologicalProof_app.
    * by apply elem_of_app; left; left.
    * by apply elem_of_app; right; left.
Qed.

Definition ml_tautology_to_proof_rev  (ϕ : Pattern) (proof : list Pattern)
  (Hproof : MLTautologicalProof (ϕ :: proof)) :  MLTautology ϕ.
Proof.
  remember (length (ϕ :: proof)) as n.
  revert ϕ proof Hproof Heqn.
  induction n as [n Hind] using (well_founded_induction_type lt_wf).
  intros; inversion Hproof
    as [| | ? ? ? ? Hpf Hmp Hϕ0 Hψ]; subst.
  + by apply ml_tauto_axiom.
  + apply elem_of_list_split_alt in Hϕ0.
    assert (Hproof_ϕ0 : MLTautologicalProof (ϕ0 ::  drop_until_eq ϕ0 proof))
      by (subst; eapply MLTautologicalProof_suffix; done).
    apply (f_equal length) in Hϕ0.
    apply elem_of_list_split_alt in Hψ.
    assert (Hproof_ψ : MLTautologicalProof (ψ :: drop_until_eq ψ proof))
      by (subst; eapply MLTautologicalProof_suffix; done).
    apply (f_equal length) in Hψ.
    rewrite app_length in Hϕ0, Hψ; cbn in Hϕ0, Hψ.
    apply ml_tauto_modus_ponens with ϕ0 ψ; [..| done]; eapply Hind.
    2,3,5,6: done.
    all: cbn; lia.
Qed.

End sec_basic_tautological_proof.
