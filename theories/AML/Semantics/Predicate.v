From stdpp Require Import prelude.
From Coq Require Import Classical.
From sets Require Import Ensemble.
From AML Require Import Signature Pattern Variables PatternClosureProps.
From AML Require Import Structure Valuation PropositionalPatternValuation PatternValuation.
From AML Require Import Satisfaction SemanticConsequences.

Section sec_predicates.

Context `{signature}.

Definition spredicate (s : Structure) (ϕ : Pattern) : Prop :=
  forall (e : Valuation), CrispSet (pattern_valuation s e ϕ).

Definition predicate (ϕ : Pattern) : Prop :=
  forall s : Structure, spredicate s ϕ.

#[export] Instance spredicate_bot s : BotClosed (spredicate s).
Proof. by constructor; intro e; left; apply pattern_valuation_bot. Qed.

#[export] Instance spredicate_impl s : ImplClosed (spredicate s).
Proof.
  constructor; intros ϕ ψ Hϕ Hψ e.
  destruct (Hϕ e) as [Hϕb | Hϕt];
    [by right; apply esatisfies_impl_classic; rewrite Hϕb; apply empty_subseteq |].
  destruct (Hψ e) as [Hψb | Hψt];
    [| by right; apply esatisfies_impl_classic; rewrite Hψt].
  left. rewrite pattern_valuation_impl_alt_classic, Hϕt, Hψb by typeclasses eauto.
  apply elem_of_equiv_empty; intros x; rewrite elem_of_union, elem_of_complement.
  by unfold top; cbn; intros [].
Qed.

#[export] Instance spredicate_ex_classic s : ExClosed (spredicate s).
Proof.
  constructor; intros x ϕ Hϕ e.
  destruct (classic (exists v, pattern_valuation s (valuation_eupdate e x v) ϕ ≡ top idomain))
    as [[v Hv] | Hnv].
  - by right; apply esatisfies_ex_elim; eexists.
  - left; cbn; apply empty_indexed_union; intro a.
    eapply not_ex_all_not with (n := a) in Hnv.
    by destruct (Hϕ (valuation_eupdate e x a)).
Qed.

#[export] Instance predicate_bot : BotClosed predicate.
Proof. by constructor; intro s; apply bot_closed. Qed.

#[export] Instance predicate_impl : ImplClosed predicate.
Proof.
  by constructor; intros ϕ ψ Hϕ Hψ s; apply impl_closed;
    [apply Hϕ | apply Hψ].
Qed.

#[export] Instance predicate_ex : ExClosed predicate.
Proof. by constructor; intros x ϕ Hϕ s; apply ex_closed, Hϕ. Qed.

Record ClosedPredicate (ϕ : Pattern) : Prop :=
{
  cp_closed_pattern :> ClosedPattern ϕ;
  cp_predicate : predicate ϕ
}.

#[export] Instance closed_predicate_bot : BotClosed ClosedPredicate.
Proof. by constructor; split; apply bot_closed. Qed.

#[export] Instance closed_predicate_impl : ImplClosed ClosedPredicate.
Proof. by constructor; intros ϕ ψ [] []; split; apply impl_closed. Qed.

#[export] Instance closed_predicate_ex : ExClosed ClosedPredicate.
Proof. by constructor; intros x ϕ []; split; apply ex_closed. Qed.

Context `{Set_ Pattern PatternSet}.

Definition set_closed_predicate (Gamma : PatternSet) : Prop :=
  forall ϕ, ϕ ∈ Gamma -> ClosedPredicate ϕ.

Lemma set_pattern_valuation_closed_predicate_crisp_classic Gamma s e :
  set_closed_predicate Gamma ->
  CrispSet (set_pattern_valuation s e Gamma).
Proof.
  intros HGamma.
  destruct (classic (set_pattern_valuation s e Gamma ≡ top idomain)) as [| Hval];
    [by right | left].
  apply elem_of_equiv_empty; intro a; contradict Hval.
  apply top_filtered_intersection; intros ϕ Hϕ.
  rewrite elem_of_set_pattern_valuation in Hval.
  specialize (Hval _ Hϕ).
  destruct (HGamma _ Hϕ); destruct (cp_predicate0 s e) as [Heqv |]; [| done].
  by rewrite Heqv in Hval.
Qed.

Lemma set_closed_predicate_pattern Gamma :
  set_closed_predicate Gamma -> set_closed_pattern Gamma.
Proof. by intros Hpreds ϕ Hϕ; apply Hpreds. Qed.

Lemma set_local_semantic_consequence_global_closed_predicate Gamma ϕ :
  set_closed_predicate Gamma ->
    set_local_semantic_consequence Gamma ϕ
      <->
    Gamma ⊧ ϕ.
Proof.
  by intro HGamma; eapply set_local_semantic_consequence_global_closed_pattern,
    set_closed_predicate_pattern.
Qed.

Lemma set_strong_semantic_consequence_local_closed_predicate Gamma ϕ :
  set_closed_predicate Gamma ->
    set_strong_semantic_consequence Gamma ϕ
      <->
    set_local_semantic_consequence Gamma ϕ.
Proof.
  intro HGamma; split; [by apply set_strong_semantic_consequence_local |].
  intros Hlocal s e a Ha.
  destruct (set_pattern_valuation_closed_predicate_crisp_classic Gamma s e HGamma) as
    [Hrew | Htop]; [by rewrite Hrew in Ha |].
  by apply Hlocal; [apply set_esatisfies_set_pattern_valuation |].
Qed.

End sec_predicates.
