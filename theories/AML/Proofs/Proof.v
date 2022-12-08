From stdpp Require Import prelude fin_maps.
From AML Require Import Signature Pattern Variables Substitution.
From AML.Proofs Require Import TautologicalProof ProofSystem Theorems.
From AML.Semantics Require Import Tautology.

Section sec_proofs.

Context
  `{signature}
  `{Set_ Pattern PatternSet}
  (single_premise_rule : Pattern -> Pattern -> Prop)
  .

Inductive MLProof (Gamma : PatternSet) : list Pattern -> Prop :=
| ml_empty_proof : MLProof Gamma []
| ml_proof_assumption :
    forall proof ϕ, MLProof Gamma proof ->
        ϕ ∈ Gamma ->
        MLProof Gamma (ϕ :: proof)
| ml_proof_tautology :
    forall proof ϕ, MLProof Gamma proof ->
        Tautology ϕ ->
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
    single_premise_rule ϕ ψ ->
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
  Gamma ⊢[single_premise_rule] ϕ
    <->
  exists proof, MLProof Gamma (ϕ :: proof).
Proof.
  split.
  - induction 1.
    + by exists []; apply ml_proof_assumption; [constructor |].
    + by exists []; apply ml_proof_tautology; [constructor |].
    + by exists []; apply ml_proof_axiom; [constructor |].
    + destruct IHMLXGammaTheorem1 as [proof_ϕ Hproof_ϕ].
      destruct IHMLXGammaTheorem2 as [proof_ψ Hproof_ψ].
      exists ((ϕ :: proof_ϕ) ++ ψ :: proof_ψ). 
      apply ml_proof_modus_ponens with ϕ ψ.
      * by apply MLProof_app.
      * done.
      * by apply elem_of_app; left; left.
      * by apply elem_of_app; right; left.
    + destruct IHMLXGammaTheorem as [proof_ϕ Hproof_ϕ].
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

Section sec_elaborated_proof.

Context
  `{signature}
  `{Set_ Pattern PatternSet}
  `{FinMap string StringMap}.


Inductive ElaboratedProofStep:=
| eps_assumpmtion : forall (idx : nat), ElaboratedProofStep
| eps_tautology : forall τ : Pattern, ElaboratedProofStep
| eps_ax_ex_quantifier : forall (x y : EVar) (ϕ : Pattern), ElaboratedProofStep
| eps_propagation_bot_l : forall (ϕ : Pattern), ElaboratedProofStep
| eps_propagation_bot_r : forall (ϕ : Pattern), ElaboratedProofStep
| eps_propagation_or_l : forall (ϕ_or_l ψ_or_r χ_app_r : Pattern), ElaboratedProofStep
| eps_propagation_or_r : forall (ϕ_or_l ψ_or_r χ_app_l : Pattern), ElaboratedProofStep
| eps_propagation_ex_l : forall (x : EVar) (ϕ_ex χ_app_r : Pattern), ElaboratedProofStep
| eps_propagation_ex_r : forall (x : EVar) (ϕ_ex χ_app_l : Pattern), ElaboratedProofStep
| eps_pre_fixpoint : forall (X : SVar) (ϕ_mu : Pattern), ElaboratedProofStep
| eps_existence : forall (x : EVar), ElaboratedProofStep
| eps_singleton_variable : forall (x : EVar) (phi : Pattern) (C1 C2 : AppContext),
    ElaboratedProofStep
| eps_ex_quantifier : forall (n : nat) (x : EVar), ElaboratedProofStep
| eps_framing_l : forall (n : nat) (chi : Pattern), ElaboratedProofStep 
| eps_framing_r : forall (n : nat) (chi : Pattern), ElaboratedProofStep 
| eps_set_variable_substitution : forall (n : nat) (psi : Pattern),
    ElaboratedProofStep
| eps_knaster_tarsky : forall (n : nat) (X : SVar) (phi : Pattern), ElaboratedProofStep
| eps_modus_ponens : forall (n_impl n_premise : nat), ElaboratedProofStep
.

End sec_elaborated_proof.

Section sec_derived_rules.

End sec_derived_rules.
