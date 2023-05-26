From Coq Require Import Classical.
From stdpp Require Import prelude.
From sets Require Import Functions Ensemble.

Parameters
  (Element : Type)
  (app : Element -> Element -> Ensemble Element).

Definition Pattern : Type := Ensemble Element.

Lemma complement_empty_top : complement ∅ ≡ top Element.
Proof.
  split; [done |].
  by rewrite elem_of_complement; set_solver.
Qed.

Declare Scope ml_scope.
Open Scope ml_scope.

Definition pattern_app (B C : Pattern) : Pattern :=
    fun x => exists b, b ∈ B /\ exists c, c ∈ C /\ x ∈ app b c.
Infix "$$" := pattern_app (at level 11) : ml_scope.

Lemma elem_of_pattern_app a B C :
  a ∈ pattern_app B C <-> exists b, b ∈ B /\ exists c, c ∈ C /\ a ∈ app b c.
Proof. done. Qed.

#[export] Instance pattern_app_Proper_subseteq_l : Proper ((⊆) ==> (≡) ==> (⊆)) pattern_app.
Proof.
  intros B C Hbc D E Hde.
  intros a (b & Hb & d & Hd & Ha).
  by exists b; split; [apply Hbc | exists d; split; [apply Hde |]].
Qed.

#[export] Instance pattern_app_Proper_subseteq_r : Proper ((≡) ==> (⊆) ==> (⊆)) pattern_app.
Proof.
  intros B C Hbc D E Hde.
  intros a (b & Hb & d & Hd & Ha).
  by exists b; split; [apply Hbc | exists d; split; [apply Hde |]].
Qed.

#[export] Instance pattern_app_Proper_subseteq : Proper ((⊆) ==> (⊆) ==> (⊆)) pattern_app.
Proof.
  intros B C Hbc D E Hde.
  by transitivity (pattern_app B E); [rewrite Hde | rewrite Hbc].
Qed.

#[export] Instance pattern_app_Proper : Proper ((≡) ==> (≡) ==> (≡)) pattern_app.
Proof.
  intros B C Hbc D E Hde a; rewrite ! elem_of_pattern_app.
  by setoid_rewrite Hbc; setoid_rewrite Hde.
Qed.

Definition pattern_impl (B C : Pattern) : Pattern := complement B ∪ C.
Notation "x →ₚ y" := (pattern_impl x y) (at level 55, right associativity) : ml_scope.

Definition pattern_ex (φ : Element -> Pattern) : Pattern := indexed_union φ.
Notation "'∃ₚ' x .. y , P" := (pattern_ex (λ x, .. (pattern_ex (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∃ₚ  x  ..  y ,  P") : ml_scope.

Definition pattern_mu (φ : Pattern -> Pattern) : Pattern := lfp φ.
Notation "'μₚ' x .. y , P" := (pattern_mu (λ x, .. (pattern_mu (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "μₚ  x  ..  y ,  P") : ml_scope.

Notation "⊥ₚ" := (μₚ X, X) (at level 37) : ml_scope.

Notation "¬ₚ x" := (x →ₚ ⊥ₚ) (at level 40) : ml_scope.
Notation "⊤ₚ" := (¬ₚ ⊥ₚ) (at level 37) : ml_scope.
Notation "x ∨ₚ y" := (¬ₚ x →ₚ y) (at level 53, left associativity) : ml_scope.
Notation "x ∧ₚ y" := (¬ₚ(¬ₚ x ∨ₚ ¬ₚ y)) (at level 50, left associativity) : ml_scope.
Notation "x ↔ₚ y" := ((x →ₚ y) ∧ₚ (y →ₚ x)) (at level 57, no associativity) : ml_scope.

Notation "'∀ₚ' x .. y , P" := (¬ₚ ∃ₚ x, ¬ₚ .. (¬ₚ ∃ₚ y, ¬ₚ P) .. )
  (at level 200, x binder, y binder, right associativity,
  format "∀ₚ  x  ..  y ,  P") : ml_scope.

Definition pattern_nu (φ : Pattern -> Pattern) : Pattern :=
  ¬ₚ μₚ X, ¬ₚ φ (¬ₚ X).

Notation "'νₚ' x .. y , P" := (pattern_nu (λ x, .. (pattern_nu (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "νₚ  x  ..  y ,  P") : ml_scope.


Definition Is_top (φ : Pattern) : Prop := φ ≡ ⊤ₚ.

Coercion Is_top : Pattern >-> Sortclass.
Global Hint Unfold Is_top : core.

Lemma top_true (a : Element) : a ∈ ⊤ₚ.
Proof.
  unfold pattern_impl; rewrite elem_of_union, elem_of_complement.
  by destruct (classic (a ∈ ⊥ₚ)); set_solver.
Qed.

Lemma pattern_to_sets (φ : Pattern) : φ <-> forall x, x ∈ φ.
Proof.
  split; unfold Is_top.
  - intros Heq x; rewrite Heq; apply top_true.
  - intro Hphi; split; [by intros; apply top_true |].
    by intro; apply Hphi.
Qed.

Lemma pattern_impl_to_inclusion (φ ψ : Pattern) : φ ⊆ ψ <-> φ →ₚ ψ.
Proof.
  rewrite pattern_to_sets; unfold pattern_impl.
  apply forall_proper; intro.
  rewrite elem_of_union, elem_of_complement.
  split.
  - intros Hall.
    destruct (classic (x ∈ φ)); [| by left].
    by right; apply Hall.
  - by intros [] ?.
Qed.

Lemma pattern_bot_to_empty : ⊥ₚ ≡ ∅.
Proof.
  split; [| by set_solver].
  unfold pattern_mu, lfp, pre_fixpoint.
  rewrite elem_of_filtered_intersection; cbn.
  by intros Hbot; apply Hbot.
Qed.

Lemma pattern_top_to_top : ⊤ₚ ≡ top Element.
Proof.
  split; [by set_solver |].
  unfold pattern_impl; rewrite pattern_bot_to_empty.
  by rewrite (union_empty_r (complement ∅)), complement_empty_top.
Qed.

Lemma pattern_or_to_union (φ ψ : Pattern) : φ ∨ₚ ψ ≡ φ ∪ ψ.
Proof.
  intro x; unfold pattern_impl.
  repeat rewrite !elem_of_union, !elem_of_complement.
  rewrite pattern_bot_to_empty.
  split; (intros [Hphi |]; [| by right]); left.
  - by destruct (classic (x ∈ φ)); [| contradict Hphi; left].
  - by intros [].
Qed.

Lemma pattern_and_to_intersection (φ ψ : Pattern) : φ ∧ₚ ψ ≡ φ ∩ ψ.
Proof.
  intro x; unfold pattern_impl.
  repeat (rewrite !complement_union_classic || rewrite !complement_twice_classic ||
  rewrite !complement_intersection_classic).
  rewrite !pattern_bot_to_empty.
  rewrite (union_empty_r (φ ∩ complement ∅)).
  rewrite (union_empty_r ((φ ∩ complement ∅) ∩ (ψ ∩ complement ∅))).
  rewrite !complement_empty_top.
  by set_solver.
Qed.

Lemma pattern_neg_to_complement (φ : Pattern) : ¬ₚ φ ≡ complement φ.
Proof.
  intro; unfold pattern_impl.
  rewrite pattern_bot_to_empty.
  by rewrite (union_empty_r (complement φ)).
Qed.

Lemma lukasiewicz (A B C D : Pattern) :
  ((A →ₚ B) →ₚ C) →ₚ (C →ₚ A) →ₚ (D →ₚ A).
Proof.
  apply pattern_to_sets; intro.
  unfold pattern_impl.
  repeat rewrite !elem_of_union, !elem_of_complement.
  destruct (classic (x ∈ A)); [by do 3 right |].
  destruct (classic (x ∈ D)); [| by do 2 right; left].
  destruct (classic (x ∈ C)); [by right; left; intros [] |].
  left.
  intros [Hneg |]; [| done].
  by contradict Hneg; left.
Qed.

Lemma modus_ponens (φ ψ : Pattern) : φ → φ →ₚ ψ → ψ.
Proof.
  rewrite !pattern_to_sets.
  unfold pattern_impl.
  intros Hphi Himpl x; specialize (Hphi x). specialize (Himpl x).
  rewrite elem_of_union, elem_of_complement in Himpl.
  by destruct Himpl.
Qed.

Ltac ml_apply impl :=
  eapply modus_ponens; [| by apply impl].

Ltac ml_apply_in impl H :=
  eapply modus_ponens in H; [by apply impl |].

Lemma ex_quantifier (φ : Element -> Pattern) (y : Element) :
  φ y →ₚ ∃ₚ x, (φ x).
Proof.
  intro a.
  unfold pattern_impl, pattern_ex; rewrite !elem_of_union,
    !elem_of_complement, elem_of_indexed_union.
  split; [by destruct (classic (a ∈ ⊥ₚ)); set_solver |].
  intros _.
  destruct (classic (a ∈ φ y)); [| by left].
  by right; eexists.
Qed.

Lemma app_False_l (φ : Pattern) : (φ $$ ⊥ₚ) →ₚ ⊥ₚ.
Proof.
  apply pattern_impl_to_inclusion.
  rewrite !pattern_bot_to_empty.
  intro; rewrite elem_of_pattern_app; intros (b & Hb & c & Hc & _).
  by set_solver.
Qed.

Lemma app_False_r (φ : Pattern) : (⊥ₚ $$ φ) →ₚ ⊥ₚ.
Proof.
  apply pattern_impl_to_inclusion.
  rewrite !pattern_bot_to_empty.
  intro; rewrite elem_of_pattern_app; intros (b & Hb & _).
  by set_solver.
Qed.

Lemma app_or_l (φ ψ χ : Pattern) : (φ ∨ₚ ψ) $$ χ →ₚ φ $$ χ ∨ₚ ψ $$ χ.
Proof.
  apply pattern_impl_to_inclusion.
  rewrite !pattern_or_to_union.
  intro x; rewrite elem_of_union, !elem_of_pattern_app.
  intros (b & Hb & c & Hc & Happ).
  apply elem_of_union in Hb as [].
  - by left; do 2 (eexists; split; [done |]).
  - by right; do 2 (eexists; split; [done |]).
Qed.

Lemma app_or_r (φ ψ χ : Pattern) : χ $$ (φ ∨ₚ ψ) →ₚ χ $$ φ ∨ₚ χ $$ ψ.
Proof.
  apply pattern_impl_to_inclusion.
  rewrite !pattern_or_to_union.
  intro x; rewrite elem_of_union, !elem_of_pattern_app.
  intros (b & Hb & c & Hc & Happ).
  apply elem_of_union in Hc as [].
  - by left; do 2 (eexists; split; [done |]).
  - by right; do 2 (eexists; split; [done |]).
Qed.

Lemma app_ex_l (φ : Element -> Pattern) (ψ : Pattern) :
  (∃ₚ x, φ x) $$ ψ →ₚ ∃ₚ x, φ x $$ ψ.
Proof.
  apply pattern_impl_to_inclusion.
  intro x; unfold pattern_ex.
  rewrite elem_of_pattern_app, elem_of_indexed_union.
  intros (b & Hb & c & Hc & Happ).
  apply elem_of_indexed_union in Hb as [y Hb].
  exists y; apply elem_of_pattern_app.
  by do 2 (eexists; split; [done |]).
Qed.

Lemma app_ex_r (φ : Element -> Pattern) (ψ : Pattern) :
  ψ $$ (∃ₚ x, φ x) →ₚ ∃ₚ x, ψ $$ φ x.
Proof.
  apply pattern_impl_to_inclusion.
  intro x; unfold pattern_ex.
  rewrite elem_of_pattern_app, elem_of_indexed_union.
  intros (b & Hb & c & Hc & Happ).
  apply elem_of_indexed_union in Hc as [y Hc].
  exists y; apply elem_of_pattern_app.
  by do 2 (eexists; split; [done |]).
Qed.

Lemma pre_fixpoint (φ : Pattern -> Pattern) `{!Proper ((⊆) ==> (⊆)) φ} :
  φ (μₚ X, φ X) →ₚ μₚ X, φ X.
Proof. by apply pattern_impl_to_inclusion, knaster_tarsky_lfp_fix_sub. Qed.

Lemma existence : ∃ₚ x, {[ x ]}.
Proof.
  apply pattern_to_sets; intro x.
  unfold pattern_ex.
  apply elem_of_indexed_union.
  by exists x; apply elem_of_singleton.
Qed.

