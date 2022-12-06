From stdpp Require Import prelude.
From Coq Require Import ClassicalEpsilon.
From AML.Lib Require Import Ensemble Traces.
From AML Require Import Signature.
From AML.Syntax Require Import Pattern Variables Substitution Reachability.
From AML.Semantics Require Import Structure Valuation PatternValuation.

Section sec_transition_system.

Context
  `{ReachabilitySignature}
  (s : Structure)
  .

Section sec_pattern_valuation_next.

Definition pattern_valuation_EX_fn : idomain -> Ensemble idomain :=
  pattern_valuation_fn s inhabitant (EX (PEVar inhabitant)) inhabitant.

Definition pattern_valuation_EX_functor := image pattern_valuation_EX_fn.

Lemma pattern_valuation_EX_functor_unfold A :
  pattern_valuation_EX_functor A
    ≡
  ext_iapp s (isigma next) A.
Proof.
  unfold pattern_valuation_EX_functor.
  unfold pattern_valuation_EX_fn, image.
  unfold pattern_valuation_fn.
  intro a; rewrite elem_of_filtered_union.
  setoid_rewrite pattern_valuation_app.
  setoid_rewrite elem_of_ext_iapp.
  unfold pattern_valuation.
  setoid_rewrite elem_of_singleton.
  cbn; unfold Functions.fn_update.
  case_decide; [| done].
  by set_solver.
Qed.

Lemma pattern_valuation_EX_fn_unfold a :
  pattern_valuation_EX_fn a
    ≡
  ext_iapp s (isigma next) {[a]}.
Proof.
  rewrite (image_singleton pattern_valuation_EX_fn).
  by apply pattern_valuation_EX_functor_unfold.
Qed.

Definition pattern_valuation_EX_functor_rev := preimage pattern_valuation_EX_fn.
Definition pattern_valuation_EX_functor_fiber := fiber pattern_valuation_EX_fn.

Lemma elem_of_pattern_valuation_EX_functor_fiber a b :
  a ∈ pattern_valuation_EX_functor_fiber b
    <->
  b ∈ pattern_valuation_EX_fn a.
Proof. by apply elem_of_fiber. Qed.

End sec_pattern_valuation_next.

Definition transition (a b : idomain) : Prop := a ∈ pattern_valuation_EX_fn b.
Definition stuck (a : idomain) : Prop := pattern_valuation_EX_functor_fiber a ≡ ∅.

Lemma stuck_iff_no_transition a :
  stuck a <-> forall b, ~ transition a b.
Proof.
  unfold stuck, transition, equiv, set_equiv_instance.
  setoid_rewrite elem_of_pattern_valuation_EX_functor_fiber.
  by set_solver.
Qed.

Section sec_traces.

Definition validTEX : trace idomain -> Prop :=
  ForAllSuffixes
    (fun tr => match tr with
    | Tnil a => stuck a
    | Tcons a tr => transition a (hd tr)
    end).

Lemma validTEX_nil : forall a, stuck a -> validTEX (Tnil a).
Proof. by intros; apply Forall_nil. Qed.

Lemma validTEX_delay : forall a tr,
  transition a (hd tr) -> validTEX tr -> validTEX (Tcons a tr).
Proof. by intros; eapply Forall_delay. Qed.

Definition trace_all_path_finally_set (P : Ensemble idomain) (a : idomain) : Prop :=
  forall tr : trace idomain, hd tr = a -> validTEX tr ->
  Exists1 (fun b : idomain => b ∈ P) tr.

End sec_traces.

Section sec_always_finally.

Context
  (e : Valuation)
  (ψ : Pattern)
  .

Section sec_always_finally_traces.

Definition trace_all_path_finally_pattern : Ensemble idomain :=
  trace_all_path_finally_set (pattern_valuation s e ψ).

End sec_always_finally_traces.

Section sec_fix_points.

Context
  (X : SVar)
  (HX_free : X ∉ FSV ψ)
  .

Lemma pattern_valuation_functor_EX ϕ A :
  pattern_valuation_functor s e (EX ϕ) X A
    ≡
  pattern_valuation_EX_functor (pattern_valuation_functor s e ϕ X A).
Proof.
  unfold EX.
  rewrite pattern_valuation_functor_app.
  rewrite pattern_valuation_functor_free at 1 by apply not_elem_of_empty.
  cbn.
  by rewrite pattern_valuation_EX_functor_unfold.
Qed.

Definition phi_or_next_on_all_paths_functor :=
  pattern_valuation_functor s e (ψ ∨ₚ (AX (PSVar X) ∧ₚ can_transition)) X.

Lemma elem_of_phi_or_next_on_all_paths_functor x A :
  x ∈ phi_or_next_on_all_paths_functor A
    <->
  x ∈ pattern_valuation s e ψ
    \/
  ∅ ⊂ pattern_valuation_EX_functor_fiber x ⊆ A.
Proof.
  unfold phi_or_next_on_all_paths_functor.
  rewrite pattern_valuation_functor_or,
    pattern_valuation_functor_and.
  unfold AX, can_transition; rewrite pattern_valuation_functor_neg,
    ! pattern_valuation_functor_EX, ! pattern_valuation_EX_functor_unfold,
    pattern_valuation_functor_neg, pattern_valuation_functor_top.
  cbn; rewrite Functions.fn_update_eq.
  rewrite elem_of_union, pattern_valuation_functor_free at 1 by done.
  apply or_iff_compat_l.
  rewrite elem_of_intersection, elem_of_complement, !elem_of_ext_iapp.
  split.
  - intros (Hnex & b & Hb & c & _ & Hx).
    assert
      (Hall : forall b, b ∈ isigma next ->
        forall c, x ∈ iapp b c -> c ∈ A).
    {
      intros b' Hb' c' Hc'.
      apply not_ex_all_not with (n := b') in Hnex.
      apply not_and_or in Hnex.
      pose proof (Hnex' := or_to_imply _ _ Hnex Hb').
      apply not_ex_all_not with (n := c') in Hnex'.
      destruct (classic (c' ∈ A)); [done |].
      contradict Hnex'; split; [| done].
      by apply elem_of_complement.
    }
    repeat split.
    + apply empty_subseteq.
    + intros Hsub.
      cut (exists a, a ∈ pattern_valuation_EX_functor_fiber x).
      { by intros [a Ha]; apply Hsub in Ha; contradict Ha; apply not_elem_of_empty. }
      specialize (Hall b Hb c Hx).
      exists c; apply elem_of_pattern_valuation_EX_functor_fiber.
      rewrite pattern_valuation_EX_fn_unfold, elem_of_ext_iapp.
      by set_solver.
    + intros a.
      rewrite elem_of_pattern_valuation_EX_functor_fiber,
        pattern_valuation_EX_fn_unfold, elem_of_ext_iapp.
      by set_solver.
  - intros [[_ Hnempty] HsubA].
    split.
    + intros (b & Hb & c & Hnc & Hx).
      rewrite elem_of_complement in Hnc.
      contradict Hnc; apply HsubA, elem_of_pattern_valuation_EX_functor_fiber.
      rewrite pattern_valuation_EX_fn_unfold, elem_of_ext_iapp.
      by set_solver.
    + destruct (classic (exists a, a ∈ pattern_valuation_EX_functor_fiber x))
        as [[a Ha] | Hnex].
      * rewrite elem_of_pattern_valuation_EX_functor_fiber,
          pattern_valuation_EX_fn_unfold, elem_of_ext_iapp in Ha.
        by set_solver.
      * contradict Hnempty; intros a Ha.
        by contradict Hnex; eexists.
Qed.

Lemma not_stuck_pattern_valuation_EX_functor_fiber x :
  ~ stuck x <-> ∅ ⊂ pattern_valuation_EX_functor_fiber x.
Proof. by set_solver. Qed.

Lemma not_stuck_transition x :
  ~ stuck x <-> exists y, transition x y.
Proof.
  unfold stuck, transition.
  unfold equiv, set_equiv_instance.
  setoid_rewrite elem_of_pattern_valuation_EX_functor_fiber.
  split; [| by set_solver].
  intros Hnall; apply not_all_ex_not in Hnall as [y Hy].
  by apply not_and_or in Hy as [Hy | Hy];
      apply imply_to_and in Hy; set_solver.
Qed.

Lemma AX_subseteq x A :
  pattern_valuation_EX_functor_fiber x ⊆ A
    <->
  forall y, transition x y -> y ∈ A.
Proof.
  unfold subseteq, set_subseteq_instance.
  setoid_rewrite elem_of_pattern_valuation_EX_functor_fiber.
  by set_solver.
Qed.

Lemma elem_of_phi_or_next_on_all_paths_functor_alt x A :
  x ∈ phi_or_next_on_all_paths_functor A
    <->
  x ∈ pattern_valuation s e ψ
    \/
  (~ stuck x /\ forall y, transition x y -> y ∈ A).
Proof.
  by rewrite elem_of_phi_or_next_on_all_paths_functor,
    not_stuck_pattern_valuation_EX_functor_fiber, <- AX_subseteq.
Qed.

Lemma trace_all_path_finally_pattern_pre_fixpoint :
  pre_fixpoint phi_or_next_on_all_paths_functor trace_all_path_finally_pattern.
Proof.
  intro a; rewrite elem_of_phi_or_next_on_all_paths_functor_alt.
  intros [Ha | [Hnot_stuck Hall]] tr Hhd Htr;
    [by subst; apply Exists_now |].
  inversion Htr as [? Hstuck | ? ? Hfirst Hrest]; subst; [done |].
  by eapply Exists_delay, Hall.
Qed.

Lemma trace_all_path_finally_pattern_post_fixpoint :
  post_fixpoint phi_or_next_on_all_paths_functor trace_all_path_finally_pattern.
Proof.
  intro a; rewrite elem_of_phi_or_next_on_all_paths_functor_alt.
  intro Hall.
  classical_right.
  split.
  - intro.
    specialize (Hall (Tnil a)).
    by feed specialize Hall; [| eapply validTEX_nil | inversion Hall].
  - intros b Hb tr <- Htr.
    specialize (Hall (Tcons a tr)).
    by feed specialize Hall; [| eapply validTEX_delay | inversion Hall].
Qed.

Lemma trace_all_path_finally_pattern_fixpoint :
  fixpoint phi_or_next_on_all_paths_functor trace_all_path_finally_pattern.
Proof.
  split.
  - apply (trace_all_path_finally_pattern_pre_fixpoint x).
  - apply (trace_all_path_finally_pattern_post_fixpoint x).
Qed.

Lemma not_elem_of_phi_or_next_on_all_paths_functor_pre_fixpoint
  A (Hpre: pre_fixpoint phi_or_next_on_all_paths_functor A) :
  forall a, a ∉ A -> a ∉ pattern_valuation s e ψ.
Proof.
  intros a Hna; contradict Hna; apply Hpre.
  by apply elem_of_phi_or_next_on_all_paths_functor; left.
Qed.

Lemma not_elem_of_phi_or_next_on_all_paths_functor_pre_fixpoint_not_stuck
  A (Hpre: pre_fixpoint phi_or_next_on_all_paths_functor A)
  (a: idomain)
  (Hna: a ∉ A)
  (Hnot_stuck : ~ stuck a)
  : exists a', a' ∉ A /\ transition a a'.
Proof.
  specialize (Hpre a).
   apply imply_to_or in Hpre as [Hpre |]; [| done].
  rewrite elem_of_phi_or_next_on_all_paths_functor_alt in Hpre.
  apply not_or_and in Hpre as [_ Hpre].
  apply not_and_or in Hpre as [| Hpre]; [done |].
  apply not_all_ex_not in Hpre as [a' Ha'].
  apply imply_to_and in Ha' as [].
  by exists a'.
Qed.

Section sec_iterated_choice.

Context
  (A : Ensemble idomain)
  (choose: {a : idomain | (a ∉ A) ∧ ¬ stuck a} → idomain)
  (Hchoose_not_in: forall x : {a : idomain | (a ∉ A) ∧ ¬ stuck a}, choose x ∉ A).

CoFixpoint iterated_choice
  (a : idomain)
  (Ha : a ∉ A)
  : trace idomain
  :=
  match (excluded_middle_informative (stuck a)) with
  | left _ => Tnil a
  | right Hnot_stuck =>
    Tcons a (iterated_choice _ (Hchoose_not_in (exist _ a (conj Ha Hnot_stuck))))
  end.

Lemma iterated_choice_unfold
  (a : idomain)
  (Ha : a ∉ A)
  : iterated_choice a Ha
    =
    match (excluded_middle_informative (stuck a)) with
    | left _ => Tnil a
    | right Hnot_stuck =>
      Tcons a (iterated_choice _ (Hchoose_not_in (exist _ a (conj Ha Hnot_stuck))))
    end.
Proof. by apply trace_eq_hd_tl; done. Qed.

Lemma iterated_choice_hd (a : idomain) (Ha : a ∉ A) :
  hd (iterated_choice a Ha) = a.
Proof.
  rewrite iterated_choice_unfold.
  by destruct (excluded_middle_informative (stuck a)).
Qed.

End sec_iterated_choice.

Lemma trace_all_path_finally_pattern_least_pre_fixpoint A :
  pre_fixpoint phi_or_next_on_all_paths_functor A ->
  trace_all_path_finally_pattern ⊆ A.
Proof.
  intros Hpre.
  unfold trace_all_path_finally_pattern, trace_all_path_finally_set.
  intro a; unfold elem_of at 1, pow_set_elem_of at 1; cbn.
  intros Hall.
  destruct (classic (a ∈ A)) as [| Hna]; [done |]; exfalso.
  cut (exists tr, hd tr = a /\ validTEX tr /\
      ForAll1 (fun b => b ∉ A) tr).
  {
    intros (tr & Hhd & Htr & Hall_b).
    specialize (Hall tr Hhd Htr).
    apply Exists1_exists in Hall as (n & Hn).
    contradict Hn.
    by eapply not_elem_of_phi_or_next_on_all_paths_functor_pre_fixpoint, ForAll1_forall.
  }
  clear Hall.
  assert (Hall_ex :
   forall x : {a : idomain | a ∉ A /\ ~ stuck a},
                    exists a' : idomain, (a' ∉ A) /\ transition (` x) a').
  {
    intros (a0 & Hna0 & Hnot_stuck0).
    by apply not_elem_of_phi_or_next_on_all_paths_functor_pre_fixpoint_not_stuck.
  }
  apply choice in Hall_ex as [choose Hchoose].
  assert (Hchoose_not_in : forall x : {a : idomain | (a ∉ A) ∧ ¬ stuck a},
    choose x ∉ A) by firstorder.
  exists (iterated_choice _ choose Hchoose_not_in _ Hna).
  repeat split.
  - by apply iterated_choice_hd.
  - unfold validTEX.
    revert a Hna.
    cofix CIH; intros a Hna.
    rewrite iterated_choice_unfold.
    destruct (excluded_middle_informative (stuck a)) as [| Hnstuck];
      [by apply Forall_nil |].
    apply Forall_delay.
    + rewrite iterated_choice_hd.
      change a with (` (exist (fun a => (a ∉ A) ∧ ¬ stuck a) a (conj Hna Hnstuck))).
      by apply Hchoose.
    + apply CIH.
  - revert a Hna.
    cofix CIH; intros a Hna.
    rewrite iterated_choice_unfold.
    destruct (excluded_middle_informative (stuck a));
      [by apply Forall_nil |].
    apply Forall_delay; [done |].
    by apply CIH.
Qed.

End sec_fix_points.

End sec_always_finally.

End sec_transition_system.
