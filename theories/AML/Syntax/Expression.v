From stdpp Require Import prelude.
From Coq Require Import Program.Equality.
From AML Require Import Signature.

Inductive Symbols `{signature} : Type :=
| evar : EVar  -> Symbols
| svar : SVar -> Symbols
| impl : Symbols
| ex : Symbols
| mu : Symbols
| app : Symbols
| op : Sigma -> Symbols.

Section sec_expression.

Context `{signature}.

Definition Expression : Type := list Symbols.

Inductive AtomicPattern : Expression -> Type :=
| atomic_evar : forall e : EVar, AtomicPattern [evar e]
| atomic_svar : forall e : SVar, AtomicPattern [svar e]
| atomic_cons : forall c : Sigma, AtomicPattern [op c].

Inductive is_pattern : Expression -> Type :=
| pattern_atomic : forall e, AtomicPattern e -> is_pattern e
| pattern_app : forall ϕ ψ, is_pattern ϕ -> is_pattern ψ ->
    is_pattern ([app] ++ ϕ ++ ψ)
| pattern_impl : forall ϕ ψ, is_pattern ϕ -> is_pattern ψ ->
    is_pattern ([impl] ++ ϕ ++ ψ)
| pattern_ex : forall (x : EVar) ϕ, is_pattern ϕ ->
    is_pattern ([ex] ++ [evar x] ++ ϕ)
| pattern_mu : forall (X : SVar) ϕ, is_pattern ϕ ->
    is_pattern ([mu] ++ [svar X] ++ ϕ).

Lemma empty_is_not_pattern : is_pattern [] -> False.
Proof. by inversion 1 as [a Ha | | | |]; inversion Ha. Qed.

Lemma singleton_is_pattern_atomic : forall a,
  is_pattern [a] -> AtomicPattern [a].
Proof.
  inversion 1 as
    [ p Hp | ϕ ψ Hϕ Hψ | ϕ ψ Hϕ Hψ
    | |
    ]; subst; [done |..];
    contradict Hψ;
    replace ψ with (@nil Symbols) by (symmetry; eapply app_nil; done);
    apply empty_is_not_pattern.
Qed.

Lemma singleton_is_pattern_atomic_rev : forall a,
  AtomicPattern [a] -> is_pattern [a].
Proof. by constructor 1. Qed.

Lemma unique_readibility_pos_length : forall p, is_pattern p -> length p > 0.
Proof. by inversion 1; [inversion X0 |..]; cbn; lia. Qed.

Lemma unique_readibility_initial_segment : forall e, is_pattern e ->
  forall p, strict prefix p e -> is_pattern p -> False.
Proof.
  intros e; remember (length e) as n; revert e Heqn.
  induction n as [n IHn] using (well_founded_induction lt_wf); intros e Heqn He p Hpre Hp.
  destruct n; [by apply unique_readibility_pos_length in He; lia |].
  destruct e; [by inversion Heqn |].
  destruct Hpre as [[suf Hpre] Hproper].
  apply unique_readibility_pos_length in Hp as Hp_len.
  destruct p; [by cbn in Hp_len; lia | clear Hp_len].
  simplify_list_eq.
  destruct suf; [by contradict Hproper; simplify_list_eq | clear Hproper].
  inversion He as [ | ? ? ? ? [a Heq_app] | ? ? ? ? [a Heq_app] | | ];
    [by destruct p; inversion X|..]; subst; inversion Hp; subst.
  - by subst; inversion X1.
  - simplify_list_eq.
    apply app_eq_app in Heq_app as [suf' Hψ]; (destruct suf'; simplify_list_eq; cycle 1);
      [destruct Hψ as [[-> Hψ] | [-> Hψ]] |].
    + contradict X1; eapply IHn; cycle 2; [exact X | split |  | done].
      * by eexists.
      * intros [suf'' Heq]; simplify_list_eq.
        apply f_equal with (f := length) in Heq.
        by rewrite app_length in Heq; cbn in Heq; lia.
      * by rewrite Hψ, !app_length; cbn; rewrite app_length; cbn; lia.
    + contradict X; eapply IHn; cycle 2; [exact X1 | split |  | done].
      * by eexists.
      * intros [suf'' Heq]; simplify_list_eq.
        apply f_equal with (f := length) in Heq.
        by rewrite app_length in Heq; cbn in Heq; lia.
      * by rewrite !app_length; lia.
    + assert (ϕ = ϕ0 /\ ψ = ψ0 ++ s :: suf) as []
        by (destruct Hψ; destruct_and!; done).
      clear Hψ; subst.
      contradict X2; eapply IHn; cycle 2; [exact X0 | split |  | done].
      * by eexists.
      * intros [suf'' Heq]; simplify_list_eq.
        apply f_equal with (f := length) in Heq.
        by rewrite app_length in Heq; cbn in Heq; lia.
      * by rewrite !app_length; lia.
  - by inversion X1.
  - simplify_list_eq.
    apply app_eq_app in Heq_app as [suf' Hψ]; (destruct suf'; simplify_list_eq; cycle 1);
      [destruct Hψ as [[-> Hψ] | [-> Hψ]] |].
    + contradict X1; eapply IHn; cycle 2; [exact X | split |  | done].
      * by eexists.
      * intros [suf'' Heq]; simplify_list_eq.
        apply f_equal with (f := length) in Heq.
        by rewrite app_length in Heq; cbn in Heq; lia.
      * by rewrite Hψ, !app_length; cbn; rewrite app_length; cbn; lia.
    + contradict X; eapply IHn; cycle 2; [exact X1 | split |  | done].
      * by eexists.
      * intros [suf'' Heq]; simplify_list_eq.
        apply f_equal with (f := length) in Heq.
        by rewrite app_length in Heq; cbn in Heq; lia.
      * by rewrite !app_length; lia.
    + assert (ϕ = ϕ0 /\ ψ = ψ0 ++ s :: suf) as []
        by (destruct Hψ; destruct_and!; done).
      clear Hψ; subst.
      contradict X2; eapply IHn; cycle 2; [exact X0 | split |  | done].
      * by eexists.
      * intros [suf'' Heq]; simplify_list_eq.
        apply f_equal with (f := length) in Heq.
        by rewrite app_length in Heq; cbn in Heq; lia.
      * by rewrite !app_length; lia.
  - by inversion X0.
  - simplify_list_eq.
    contradict X0; eapply IHn; cycle 2; [exact X | split |  | done].
    + by eexists.
    + intros [suf'' Heq]; simplify_list_eq.
      apply f_equal with (f := length) in Heq.
      by rewrite app_length in Heq; cbn in Heq; lia.
    + by rewrite !app_length; lia.
  - by inversion X1.
  - simplify_list_eq.
    contradict X2; eapply IHn; cycle 2; [exact X0 | split |  | done].
    + by eexists.
    + intros [suf'' Heq]; simplify_list_eq.
      apply f_equal with (f := length) in Heq.
      by rewrite app_length in Heq; cbn in Heq; lia.
    + by rewrite !app_length; lia.
Qed.

#[export] Instance AtomicPattern_proof_irrel :
  forall e, ProofIrrel (AtomicPattern e).
Proof. intros e [] He2; by dependent destruction He2. Qed.

#[export] Instance is_pattern_proof_irrel :
  forall e, ProofIrrel (is_pattern e).
Proof.
  intros e He1 .
  induction He1; intro He2; dependent destruction He2; try (by inversion a).
  - by rewrite (proof_irrel a a0).
  - apply app_eq_app in x0 as [suf' Hψ]; (destruct suf'; simplify_list_eq; cycle 1);
      [destruct Hψ as [[-> Hψ] | [-> Hψ]] |].
    + exfalso.
      eapply unique_readibility_initial_segment;
        [exact He2_1 | split; [by eexists |] | exact He1_1].
      intros [suf'' Heq]; simplify_list_eq.
      apply f_equal with (f := length) in Heq.
      by rewrite app_length in Heq; cbn in Heq; lia.
    + exfalso.
      eapply unique_readibility_initial_segment;
        [exact He1_1 | split; [by eexists |] | exact He2_1].
      intros [suf'' Heq]; simplify_list_eq.
      apply f_equal with (f := length) in Heq.
      by rewrite app_length in Heq; cbn in Heq; lia.
    + assert (ϕ0 = ϕ /\ ψ0 = ψ) as [-> ->]
        by (destruct Hψ; destruct_and!; done).
      by rewrite (IHHe1_1 He2_1), (IHHe1_2 He2_2), x.
  - apply app_eq_app in x0 as [suf' Hψ]; (destruct suf'; simplify_list_eq; cycle 1);
      [destruct Hψ as [[-> Hψ] | [-> Hψ]] |].
    + exfalso.
      eapply unique_readibility_initial_segment;
        [exact He2_1 | split; [by eexists |] | exact He1_1].
      intros [suf'' Heq]; simplify_list_eq.
      apply f_equal with (f := length) in Heq.
      by rewrite app_length in Heq; cbn in Heq; lia.
    + exfalso.
      eapply unique_readibility_initial_segment;
        [exact He1_1 | split; [by eexists |] | exact He2_1].
      intros [suf'' Heq]; simplify_list_eq.
      apply f_equal with (f := length) in Heq.
      by rewrite app_length in Heq; cbn in Heq; lia.
    + assert (ϕ0 = ϕ /\ ψ0 = ψ) as [-> ->]
        by (destruct Hψ; destruct_and!; done).
      by rewrite (IHHe1_1 He2_1), (IHHe1_2 He2_2), x.
  - by rewrite (IHHe1 He2).
  - by rewrite (IHHe1 He2).
Qed.

Inductive expression_pattern : Type :=
| ep_intro : forall e, is_pattern e -> expression_pattern.

Definition proj1_ep (ep : expression_pattern) : Expression :=
  match ep with
  | ep_intro e _ => e
  end.

Definition proj2_ep (ep : expression_pattern) : is_pattern (proj1_ep ep).
Proof. by destruct ep. Defined.

Lemma ep_eq_pi :
  forall (ep1 ep2 : expression_pattern), ep1 = ep2 <-> proj1_ep ep1 = proj1_ep ep2.
Proof.
  intros [] []; split; [by intros -> |].
  by cbn; intros ->; f_equal; apply proof_irrel.
Qed.

End sec_expression.
