From Coq Require Import Classical.
From stdpp Require Import prelude.
From sets Require Import Functions Ensemble.

(** * Approximation of a shallow embedding of AML into Coq

In this module we attempt to express AML (or, better said, an approximation of it)
as a theory over sets, and show that its axioms and proof rules
(or approximations of them) are sound for that theory of sets.

We use the [Ensemble] definition of sets as unary predicates over a fixed type
over which we instantiate Coq's <<stdpp>> classes for [Set_].

This follows quite closely the interpretation of patterns as sets, so
it should be no wonder that the axioms and rules are sound.

However, to be a shallow embedding these are the things that need to change:

- Using HOAS to encode binders and substitution.
- The positivity condition on pre-fixpoint is changed to its semantic counterpart
  - a side effect of having a shallow embedding is that one cannot perform
    syntactic checks
- Applicative contexts are modeled as functions from elements to patterns.
  Context application to patterns has collective semantics, similarly to that of
  regular application.

We assume as given a base type, called <<Element>> and a binary function <<app>>
mapping pairs of element to sets of elements.
*)

Class ShallowMLContext `(app : Element -> Element -> Ensemble Element).

Section sec_shallow_ml.

(** ** The language

Since we are embedding AML as a theory over sets, all constructs are introduced
directly through their set interpretation.
*)

Context `{app : Element -> Element -> Ensemble Element} `{!ShallowMLContext app}.

Definition Pattern : Type := Ensemble Element.

(** A context is modeled as a map from elements to patterns. *)
Definition context := Element -> Pattern.

Declare Scope sml_scope.
Open Scope sml_scope.

(*
  Pattern application is defined as the extension of <<app>> to patterns
  (as sets of elements).
*)
Definition pattern_app (B C : Pattern) : Pattern :=
    fun x => exists b : Element, b ∈ B /\ exists c : Element, c ∈ C /\ x ∈ app b c.
Infix "$$" := pattern_app (at level 11) : sml_scope.

(**
  Context application on a pattern is defined similarly to regular application
  on patterns, as the collective semantics.
*)
Definition context_app (ec : context) (ϕ : Pattern) : Pattern :=
  fun x => exists b, b ∈ ϕ /\ x ∈ ec b.

(** We define the basic application contexts. *)
Definition context_app_l (ϕ : Pattern) (e : Element) : Pattern :=
  {[ e ]} $$ ϕ.

Definition context_app_r (ϕ : Pattern) (e : Element) : Pattern :=
  ϕ $$ {[ e ]}.

Definition pattern_impl (B C : Pattern) :
  Pattern := complement B ∪ C.
Notation "x →ₛ y" := (pattern_impl x y) (at level 55, right associativity) : sml_scope.

(**
  Existential quantification is modeled using HOAS and identifying the
  existential pattern with its semantics as an indexed-union over all possible
  instances of the quantified variable.
*)
Definition pattern_ex (φ : Element -> Pattern) : Pattern := indexed_union φ.
Notation "'∃ₛ' x .. y , P" := (pattern_ex (λ x, .. (pattern_ex (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∃ₛ  x  ..  y ,  P") : sml_scope.

(**
  Mu binding is also modeled using HOAS and identifying the mu-bound pattern
  with its semantics as the Knaster-Tarski lfp of the pattern seen as a
  function from sets to sets.
*)
Definition pattern_mu (φ : Pattern -> Pattern) : Pattern := lfp φ.
Notation "'μₛ' x .. y , P" := (pattern_mu (λ x, .. (pattern_mu (λ y, P)) .. ))
  (at level 54, x binder, y binder, right associativity,
  format "μₛ  x  ..  y ,  P") : sml_scope.

(** The other connectives are derived from the base ones as in AML. *)
Notation "⊥ₛ" := (μₛ X, X) (at level 37) : sml_scope.
Notation "¬ₛ x" := (x →ₛ ⊥ₛ) (at level 40) : sml_scope.
Notation "⊤ₛ" := (¬ₛ ⊥ₛ) (at level 37) : sml_scope.
Notation "x ∨ₛ y" := (¬ₛ x →ₛ y) (at level 53, left associativity) : sml_scope.
Notation "x ∧ₛ y" := (¬ₛ(¬ₛ x ∨ₛ ¬ₛ y)) (at level 50, left associativity) : sml_scope.
Notation "x ↔ₛ y" := ((x →ₛ y) ∧ₛ (y →ₛ x)) (at level 57, no associativity) : sml_scope.

Notation "'∀ₛ' x .. y , P" := (¬ₛ ∃ₛ x, ¬ₛ .. (¬ₛ ∃ₛ y, ¬ₛ P) .. )
  (at level 200, x binder, y binder, right associativity,
  format "∀ₛ  x  ..  y ,  P") : sml_scope.

Definition pattern_nu (φ : Pattern -> Pattern) : Pattern :=
  ¬ₛ μₛ X, ¬ₛ φ (¬ₛ X).

Notation "'νₛ' x .. y , P" := (pattern_nu (λ x, .. (pattern_nu (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "νₛ  x  ..  y ,  P") : sml_scope.

(** We define truth as the pattern being equivalent to the whole set (⊤). *)
Definition Is_top (φ : Pattern) : Prop := φ ≡ ⊤ₛ.

(** The coercion to Prop allows us to write patterns as Coq propositions. *)
Coercion Is_top : Pattern >-> Sortclass.
Hint Unfold Is_top : core.

(** ** Auxiliary set-theoretical results

  The sequence of results below allow us to translate pattern truth to
  set membership.
*)

Lemma elem_of_pattern_app a B C :
  a ∈ pattern_app B C <-> exists b, b ∈ B /\ exists c, c ∈ C /\ a ∈ app b c.
Proof. done. Qed.

#[export] Instance pattern_app_Proper_subseteq_l :
  Proper ((⊆) ==> (≡) ==> (⊆)) pattern_app.
Proof.
  intros B C Hbc D E Hde.
  intros a (b & Hb & d & Hd & Ha).
  by exists b; split; [apply Hbc | exists d; split; [apply Hde |]].
Qed.

#[export] Instance pattern_app_Proper_subseteq_r :
  Proper ((≡) ==> (⊆) ==> (⊆)) pattern_app.
Proof.
  intros B C Hbc D E Hde.
  intros a (b & Hb & d & Hd & Ha).
  by exists b; split; [apply Hbc | exists d; split; [apply Hde |]].
Qed.

#[export] Instance pattern_app_Proper_subseteq :
  Proper ((⊆) ==> (⊆) ==> (⊆)) pattern_app.
Proof.
  intros B C Hbc D E Hde.
  by transitivity (pattern_app B E); [rewrite Hde | rewrite Hbc].
Qed.

#[export] Instance pattern_app_Proper :
  Proper ((≡) ==> (≡) ==> (≡)) pattern_app.
Proof.
  intros B C Hbc D E Hde a; rewrite ! elem_of_pattern_app.
  by setoid_rewrite Hbc; setoid_rewrite Hde.
Qed.

Lemma elem_of_context_app a C A :
  a ∈ context_app C A <-> exists b, b ∈ A /\ a ∈ C b.
Proof. done. Qed.

#[export] Instance context_app_Proper_subseteq :
  Proper ((=) ==> (⊆) ==> (⊆)) context_app.
Proof.
  intros ? C -> D E Hde.
  intros a (b & Hb & Ha).
  by exists b; split; [apply Hde |].
Qed.

#[export] Instance context_app_Proper :
  Proper ((=) ==> (≡) ==> (≡)) context_app.
Proof.
  intros ? C -> D E Hde a; rewrite !elem_of_context_app.
  by setoid_rewrite Hde.
Qed.

Lemma complement_empty_top : complement ∅ ≡ top Element.
Proof.
  split; [done |].
  by rewrite elem_of_complement; set_solver.
Qed.

Lemma top_true (a : Element) : a ∈ ⊤ₛ.
Proof.
  unfold pattern_impl; rewrite elem_of_union, elem_of_complement.
  by destruct (classic (a ∈ ⊥ₛ)); set_solver.
Qed.

Lemma pattern_to_sets (φ : Pattern) : φ <-> forall x, x ∈ φ.
Proof.
  split; unfold Is_top.
  - intros Heq x; rewrite Heq; apply top_true.
  - intro Hphi; split; [by intros; apply top_true |].
    by intro; apply Hphi.
Qed.

#[export] Instance Is_top_proper_subseteq : Proper ((⊆) ==> (impl)) Is_top.
Proof.
  intros A B Hincl; rewrite !pattern_to_sets.
  intros Ha e.
  by apply Hincl.
Qed.

#[export] Instance Is_top_proper : Proper ((≡) ==> (iff)) Is_top.
Proof.
  intros A B Heqv.
  apply set_equiv_subseteq in Heqv as [].
  by split; apply Is_top_proper_subseteq.
Qed.

Lemma pattern_impl_to_inclusion (φ ψ : Pattern) : φ →ₛ ψ  <-> φ ⊆ ψ.
Proof.
  rewrite pattern_to_sets; unfold pattern_impl.
  apply forall_proper; intro.
  rewrite elem_of_union, elem_of_complement.
  split; [by intros [] ? |].
  intros Hall.
  destruct (classic (x ∈ φ)); [| by left].
  by right; apply Hall.
Qed.

#[export] Instance pattern_impl_proper_subseteq :
  Proper ((⊆) --> (⊆) ==> (⊆)) pattern_impl.
Proof.
  intros A B Hab C D Hcd.
  apply complement_subseteq_proper in Hab.
  by unfold pattern_impl; set_solver.
Qed.

#[export] Instance pattern_impl_proper : Proper ((≡) ==> (≡) ==> (≡)) pattern_impl.
Proof.
  intros A B []%set_equiv_subseteq C D []%set_equiv_subseteq.
  by split; apply pattern_impl_proper_subseteq.
Qed.

Lemma pattern_ex_proper_subseteq (ϕ ψ : Element -> Pattern) :
  (forall x, ϕ x ⊆ ψ x) -> (∃ₛ x, ϕ x) ⊆ ∃ₛ x, ψ x.
Proof.
  intros Hincl e He.
  apply elem_of_indexed_union in He as [x He].
  apply elem_of_indexed_union.
  by set_solver.
Qed.

Lemma pattern_ex_proper (ϕ ψ : Element -> Pattern) :
  (forall x, ϕ x ≡ ψ x) -> (∃ₛ x, ϕ x) ≡ ∃ₛ x, ψ x.
Proof.
  intros Hincl; apply set_equiv_subseteq.
  by split; apply pattern_ex_proper_subseteq; set_solver.
Qed.

#[export] Instance pattern_ex_iff_morphism :
  Proper (pointwise_relation Element (≡) ==> (≡)) pattern_ex.
Proof. by intros ϕ ψ Heqv; apply pattern_ex_proper. Qed.

#[export] Instance pattern_ex_impl_morphism :
  Proper (pointwise_relation Element (⊆) ==> (⊆)) pattern_ex | 1.
Proof. by intros ϕ ψ Heqv; apply pattern_ex_proper_subseteq. Qed.

#[export]
Instance pattern_ex_flip_impl_morphism {A : Type} :
  Proper (pointwise_relation Element (flip (⊆)) ==> (flip (⊆))) pattern_ex | 1.
Proof. by intros ϕ ψ Heqv; apply pattern_ex_proper_subseteq. Qed.

Lemma pattern_bot_to_empty : ⊥ₛ ≡ ∅.
Proof.
  split; [| by set_solver].
  unfold pattern_mu, lfp, pre_fixpoint.
  rewrite elem_of_filtered_intersection; cbn.
  by intros Hbot; apply Hbot.
Qed.

Lemma pattern_top_to_top : ⊤ₛ ≡ top Element.
Proof.
  split; [by set_solver |].
  unfold pattern_impl; rewrite pattern_bot_to_empty.
  by rewrite (union_empty_r (complement ∅)), complement_empty_top.
Qed.

Lemma pattern_or_to_union (φ ψ : Pattern) : φ ∨ₛ ψ ≡ φ ∪ ψ.
Proof.
  intro x; unfold pattern_impl.
  repeat rewrite !elem_of_union, !elem_of_complement.
  rewrite pattern_bot_to_empty.
  split; (intros [Hphi |]; [| by right]); left.
  - by destruct (classic (x ∈ φ)); [| contradict Hphi; left].
  - by intros [].
Qed.

Lemma pattern_and_to_intersection (φ ψ : Pattern) : φ ∧ₛ ψ ≡ φ ∩ ψ.
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

Lemma pattern_neg_to_complement (φ : Pattern) : ¬ₛ φ ≡ complement φ.
Proof.
  intro; unfold pattern_impl.
  rewrite pattern_bot_to_empty.
  by rewrite (union_empty_r (complement φ)).
Qed.

Lemma context_app_l_eqv (ϕ ψ : Pattern) :
  context_app (context_app_l ψ) ϕ ≡ ϕ $$ ψ.
Proof.
  intro e; rewrite elem_of_context_app, elem_of_pattern_app.
  apply exist_proper; intro b.
  unfold context_app_l; rewrite elem_of_pattern_app.
  setoid_rewrite elem_of_singleton.
  split.
  - by intros [Hb (? & -> & c & ? & ?)]; firstorder.
  - by firstorder.
Qed.

Lemma context_app_r_eqv (ϕ ψ : Pattern) :
  context_app (context_app_r ϕ) ψ ≡ ϕ $$ ψ.
Proof.
  intro e; rewrite elem_of_context_app, elem_of_pattern_app.
  unfold context_app_r; setoid_rewrite elem_of_pattern_app.
  setoid_rewrite elem_of_singleton.
  split.
  - by intros (c & Hpsi & b & Hphi & ? & -> & He); repeat esplit.
  - by firstorder.
Qed.

(** ** The proof system *)

(**
  This axiom together with the modus-ponens rule below are complete for
  proving all tautologies of propositional logic.
*)
Lemma ax_lukasiewicz (A B C D : Pattern) :
  ((A →ₛ B) →ₛ C) →ₛ (C →ₛ A) →ₛ (D →ₛ A).
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

Lemma modus_ponens (φ ψ : Pattern) : φ → φ →ₛ ψ → ψ.
Proof.
  rewrite !pattern_to_sets.
  unfold pattern_impl.
  intros Hphi Himpl x; specialize (Hphi x). specialize (Himpl x).
  rewrite elem_of_union, elem_of_complement in Himpl.
  by destruct Himpl.
Qed.

Definition top_impl (φ ψ : Pattern) : Prop := φ →ₛ ψ.

#[export] Instance top_impl_reflexive : Reflexive top_impl.
Proof. by intro; apply pattern_impl_to_inclusion. Qed.

#[export] Instance top_impl_transitive : Transitive top_impl.
Proof.
  intros ? ? ? Ha Hb.
  apply pattern_impl_to_inclusion in Ha, Hb.
  by apply pattern_impl_to_inclusion; etransitivity.
Qed.

(** ∃-Quantifier axiom of AML *)
Lemma ex_quantifier (φ : Element -> Pattern) (y : Element) :
  φ y →ₛ ∃ₛ x, (φ x).
Proof.
  intro a.
  unfold pattern_impl, pattern_ex; rewrite !elem_of_union,
    !elem_of_complement, elem_of_indexed_union.
  split; [by destruct (classic (a ∈ ⊥ₛ)); set_solver |].
  intros _.
  destruct (classic (a ∈ φ y)); [| by left].
  by right; eexists.
Qed.

(** Axiom for Propagation of ⊥ through contexts *)
Lemma context_False (C : context) : context_app C (⊥ₛ) →ₛ ⊥ₛ.
Proof.
  apply pattern_impl_to_inclusion.
  rewrite pattern_bot_to_empty.
  intro x; rewrite elem_of_context_app; intros (? & ? & ?).
  by set_solver.
Qed.

(** Derived axiom for Propagation of ⊥ on the rhs of application *)
Lemma app_False_r (φ : Pattern) : (φ $$ ⊥ₛ) →ₛ ⊥ₛ.
Proof.
  etransitivity; [| apply (context_False (context_app_r φ))].
  by rewrite context_app_r_eqv.
Qed.

(** Derived axiom for Propagation of ⊥ on the lhs of application *)
Lemma app_False_l (φ : Pattern) : (⊥ₛ $$ φ) →ₛ ⊥ₛ.
Proof.
  etransitivity; [| apply (context_False (context_app_l φ))].
  by rewrite context_app_l_eqv.
Qed.

(** Axiom for Propagation of ∨ through contexts *)
Lemma context_or (C : context) (ϕ ψ : Pattern) :
  context_app C (ϕ ∨ₛ ψ) →ₛ  context_app C ϕ ∨ₛ context_app C ψ.
Proof.
  apply pattern_impl_to_inclusion.
  rewrite !pattern_or_to_union.
  intro x; rewrite elem_of_union, !elem_of_context_app.
  by set_solver.
Qed.

(** Derived axiom for Propagation of ∨ on the lhs of application *)
Lemma app_or_l (φ ψ χ : Pattern) : (φ ∨ₛ ψ) $$ χ →ₛ φ $$ χ ∨ₛ ψ $$ χ.
Proof.
  by transitivity (context_app (context_app_l χ) (φ ∨ₛ ψ));
    [| etransitivity; [by apply context_or |]]; rewrite !context_app_l_eqv.
Qed.

(** Derived axiom for Propagation of ∨ on the rhs of application *)
Lemma app_or_r (φ ψ χ : Pattern) : χ $$ (φ ∨ₛ ψ) →ₛ χ $$ φ ∨ₛ χ $$ ψ.
Proof.
  by transitivity (context_app (context_app_r χ) (φ ∨ₛ ψ));
    [| etransitivity; [by apply context_or |]]; rewrite !context_app_r_eqv.
Qed.

(** Axiom for Propagation of ∃ through contexts *)
Lemma context_ex (C : context) (ϕ : Element -> Pattern) :
  context_app C (∃ₛ x, ϕ x) →ₛ  ∃ₛ x, context_app C (ϕ x).
Proof.
  apply pattern_impl_to_inclusion; unfold pattern_ex.
  intro x; rewrite elem_of_indexed_union, !elem_of_context_app.
  setoid_rewrite elem_of_indexed_union.
  setoid_rewrite elem_of_context_app.
  by intros (b & [e Hb] & Hx); eexists _, _.
Qed.

(** Axiom for Propagation of ∃ on the lhs of application *)
Lemma app_ex_l (φ : Element -> Pattern) (ψ : Pattern) :
  (∃ₛ x, φ x) $$ ψ →ₛ ∃ₛ x, φ x $$ ψ.
Proof.
  by transitivity (context_app (context_app_l ψ) ((∃ₛ x, φ x)));
    [| etransitivity; [by apply context_ex |]];
    setoid_rewrite context_app_l_eqv.
Qed.

(** Axiom for Propagation of ∃ on the rhs of application *)
Lemma app_ex_r (φ : Element -> Pattern) (ψ : Pattern) :
  ψ $$ (∃ₛ x, φ x) →ₛ ∃ₛ x, ψ $$ φ x.
Proof.
  by transitivity (context_app (context_app_r ψ) ((∃ₛ x, φ x)));
    [| etransitivity; [by apply context_ex |]];
    setoid_rewrite context_app_r_eqv.
Qed.

(**
  Pre-Fixpoint axiom. The positivity condition is replaces by a [Proper]
  constraint (monotonicity).
*)
Lemma pre_fixpoint (φ : Pattern -> Pattern) `{!Proper ((⊆) ==> (⊆)) φ} :
  φ (μₛ X, φ X) →ₛ μₛ X, φ X.
Proof. by apply pattern_impl_to_inclusion, knaster_tarski_lfp_fix_sub. Qed.

(** Existence axiom *)
Lemma existence : ∃ₛ x, {[ x ]}.
Proof.
  apply pattern_to_sets; intro x.
  unfold pattern_ex.
  apply elem_of_indexed_union.
  by exists x; apply elem_of_singleton.
Qed.

(**
  Singleton Variable axiom, with contexts as modeled above.
*)
Lemma singleton_variable (C₁ C₂ : context) (ϕ : Pattern) (x : Element) :
  ¬ₛ (context_app C₁ ({[ x ]} ∧ₛ ϕ) ∧ₛ context_app C₂ ({[ x ]} ∧ₛ ¬ₛ ϕ)).
Proof.
  apply pattern_to_sets.
  intro e.
  rewrite pattern_neg_to_complement, elem_of_complement,
    pattern_and_to_intersection, elem_of_intersection.
  intros [(b & Hxphi & _) (c & Hxnphi & _)].
  rewrite pattern_and_to_intersection, elem_of_intersection, elem_of_singleton
    in *.
  destruct Hxphi as [-> Hxphi], Hxnphi as [-> Hxnphi].
  by rewrite pattern_neg_to_complement, elem_of_complement in Hxnphi.
Qed.

Lemma ex_quantifier_rule (ϕ : Element -> Pattern) (ψ : Pattern) (e : Element) :
  ϕ e →ₛ ψ -> ∃ₛ x, ϕ x →ₛ ψ.
Proof.
  intro Himpl.
  apply pattern_to_sets; intro a.
  apply elem_of_indexed_union.
  exists e.
  by revert a; apply pattern_to_sets.
Qed.

#[export] Instance framing : Proper ((=) ==> top_impl ==> top_impl) context_app.
Proof.
  intros ? C -> ϕ ψ Himpl%pattern_impl_to_inclusion.
  apply pattern_impl_to_inclusion; intro e.
  rewrite !elem_of_context_app.
  intros (b & Hb & He).
  by set_solver.
Qed.

#[export] Instance framing_flip : Proper ((=) ==> flip top_impl ==> flip top_impl) context_app.
Proof.
  intros ? C -> ϕ ψ Himpl%pattern_impl_to_inclusion.
  apply pattern_impl_to_inclusion; intro e.
  rewrite !elem_of_context_app.
  intros (b & Hb & He).
  by set_solver.
Qed.

#[export] Instance framing_app :
  Proper (top_impl ==> top_impl ==> top_impl) pattern_app.
Proof.
  intros A A' HA B B' HB; unfold top_impl.
  transitivity (A' $$ B);
    [rewrite <- !context_app_l_eqv | rewrite <- !context_app_r_eqv];
    by apply framing.
Qed.

Lemma framing_r (ϕ ψ χ : Pattern) : ϕ →ₛ ψ -> χ $$ ϕ →ₛ χ $$ ψ.
Proof. by apply framing_app. Qed.

Lemma framing_l (ϕ ψ χ : Pattern) : ϕ →ₛ ψ -> ϕ $$ χ →ₛ ψ $$ χ.
Proof. by intro; apply framing_app. Qed.

Lemma set_variable_substitution (ϕ : Pattern -> Pattern) (ψ : Pattern) :
  (forall X, ϕ X) -> ϕ ψ.
Proof. done. Qed.

Lemma knaster_tarski (ϕ : Pattern -> Pattern) (ψ : Pattern) :
  ϕ ψ →ₛ ψ -> μₛ X, ϕ X →ₛ ψ.
Proof.
  intros Hincl%pattern_impl_to_inclusion.
  apply pattern_impl_to_inclusion.
  by apply knaster_tarski_least_pre_fixpoint.
Qed.

Section sec_definedness.

Parameter def : Element.

Definition defined (phi : Pattern) : Pattern := {[def]} $$ phi.

Notation "⌈ x ⌉" := (defined x) (at level 39) : sml_scope.

Axiom definedness : ∀ₛ x, ⌈{[x]}⌉.

Definition total (phi : Pattern) : Pattern :=
  ¬ₛ⌈¬ₛ phi⌉.

Notation "⌊ x ⌋" := ({[def]} $$ x) (at level 39) : sml_scope.


End sec_definedness.
End sec_shallow_ml.

Global Hint Unfold Is_top : core.
