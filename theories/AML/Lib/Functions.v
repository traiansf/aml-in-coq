From stdpp Require Import prelude.
From Coq Require Import FunctionalExtensionality.

Definition fn_update `{EqDecision A} `(f : A -> B) (a : A) (b : B) (x : A) : B :=
  if (decide (x = a)) then b else f x.

Lemma fn_update_id `{EqDecision A} `(f : A -> B) (a : A) :
  fn_update f a (f a) = f.
Proof. by extensionality x; unfold fn_update; case_decide; subst. Qed.

Lemma fn_update_eq `{EqDecision A} `(f : A -> B) a b :
  fn_update f a b a = b.
Proof. by unfold fn_update; rewrite decide_True by done. Qed.

Lemma fn_update_comm `{EqDecision A} `(f : A -> B) a1 b1 a2 b2 :
  a1 <> a2 ->
  fn_update (fn_update f a1 b1) a2 b2
    =
  fn_update (fn_update f a2 b2) a1 b1.
Proof.
  intro Ha; extensionality x; unfold fn_update.
  by do 2 case_decide; [congruence |..].
Qed.

Fixpoint pow_compose `(f : A -> A) (n : nat) : A -> A :=
  match n with
  | 0 => id
  | S n' => f ∘ pow_compose f n'
  end.

Lemma pow_compose_one `(f : A -> A) (n : nat) :
  pow_compose f 1 = f.
Proof. by extensionality a. Qed.

Lemma compose_assoc {A B C D} (f : A -> B) (g : B -> C) (h : C -> D) :
  h ∘ (g ∘ f) = h ∘ g ∘ f.
Proof. by extensionality x. Qed.
