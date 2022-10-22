From stdpp Require Import prelude.
From Coq Require Import Classical.
From AML Require Import Ensemble.
From AML Require Import Signature Pattern Variables PatternClosureProps.
From AML Require Import Structure Valuation PropositionalPatternValuation PatternValuation.
From AML Require Import Satisfaction SemanticConsequences.

Section sec_predicates.

Context
  [sign : signature]
  (Pattern := @Pattern sign).

Definition spredicate (s : Structure) (phi : Pattern) : Prop :=
  forall (e : Valuation), CrispSet (pattern_valuation s e phi).

Definition predicate (phi : Pattern) : Prop :=
  forall s : Structure, spredicate s phi.

#[export] Instance spredicate_bot s : BotClosed (spredicate s).
Proof. by constructor; intro e; constructor 1. Qed.

#[export] Instance spredicate_impl s : ImplClosed (spredicate s).
Proof.
  constructor; intros phi psi Hphi Hpsi e.
  destruct (Hphi e) as [Hphib | Hphit];
    [by right; apply esatisfies_impl_classic; rewrite Hphib; apply empty_subseteq |].
  destruct (Hpsi e) as [Hpsib | Hpsit];
    [| by right; apply esatisfies_impl_classic; rewrite Hpsit].
  left. rewrite pattern_valuation_impl_alt_classic, Hphit, Hpsib by done.
  apply elem_of_equiv_empty; intros x; rewrite elem_of_union, elem_of_complement.
  by unfold top; cbn; intros [].
Qed.

#[export] Instance spredicate_ex_classic s : ExClosed (spredicate s).
Proof.
  constructor; intros x phi Hphi e.
  destruct (classic (exists v, pattern_valuation s (valuation_eupdate e x v) phi ≡ top idomain))
    as [[v Hv] | Hnv].
  - by right; apply esatisfies_ex_elim; eexists.
  - left; cbn; apply empty_indexed_union; intro a.
    eapply not_ex_all_not with (n := a) in Hnv.
    by destruct (Hphi (valuation_eupdate e x a)).
Qed.

#[export] Instance predicate_bot : BotClosed predicate.
Proof. by constructor; intro s; apply bot_closed. Qed.

#[export] Instance predicate_impl : ImplClosed predicate.
Proof.
  by constructor; intros phi psi Hphi Hpsi s; apply impl_closed;
    [apply Hphi | apply Hpsi].
Qed.

#[export] Instance predicate_ex : ExClosed predicate.
Proof. by constructor; intros x phi Hphi s; apply ex_closed, Hphi. Qed.

Record ClosedPredicate (phi : Pattern) : Prop :=
{
  cp_closed_pattern :> ClosedPattern phi;
  cp_predicate : predicate phi
}.

#[export] Instance closed_predicate_bot : BotClosed ClosedPredicate.
Proof. by constructor; split; apply bot_closed. Qed.

#[export] Instance closed_predicate_impl : ImplClosed ClosedPredicate.
Proof. by constructor; intros phi psi [] []; split; apply impl_closed. Qed.

#[export] Instance closed_predicate_ex : ExClosed ClosedPredicate.
Proof. by constructor; intros x phi []; split; apply ex_closed. Qed.

Context `{Set_ Pattern PatternSet}.

Definition set_closed_predicate (Gamma : PatternSet) : Prop :=
  forall phi, phi ∈ Gamma -> ClosedPredicate phi.

Lemma set_pattern_valuation_closed_predicate_crisp_classic Gamma s e :
  set_closed_predicate Gamma ->
  CrispSet (set_pattern_valuation s e Gamma).
Proof.
  intros HGamma.
  destruct (classic (set_pattern_valuation s e Gamma ≡ top idomain)) as [| Hval];
    [by right | left].
  apply elem_of_equiv_empty; intro a; contradict Hval.
  apply top_filtered_intersection; intros phi Hphi.
  rewrite elem_of_set_pattern_valuation in Hval.
  specialize (Hval _ Hphi).
  destruct (HGamma _ Hphi); destruct (cp_predicate0 s e) as [Heqv |]; [| done].
  by rewrite Heqv in Hval.
Qed.

Lemma set_closed_predicate_pattern Gamma :
  set_closed_predicate Gamma -> set_closed_pattern Gamma.
Proof. by intros Hpreds phi Hphi; apply Hpreds. Qed.

Lemma set_local_semantic_consequence_global_closed_predicate Gamma phi :
  set_closed_predicate Gamma ->
    set_local_semantic_consequence Gamma phi
      <->
    set_global_semantic_consequence Gamma phi.
Proof.
  by intro HGamma; eapply set_local_semantic_consequence_global_closed_pattern,
    set_closed_predicate_pattern.
Qed.

Lemma set_strong_semantic_consequence_local_closed_predicate Gamma phi :
  set_closed_predicate Gamma ->
    set_strong_semantic_consequence Gamma phi
      <->
    set_local_semantic_consequence Gamma phi.
Proof.
  intro HGamma; split; [by apply set_strong_semantic_consequence_local |].
  intros Hlocal s e a Ha.
  destruct (set_pattern_valuation_closed_predicate_crisp_classic Gamma s e HGamma) as
    [Hrew | Htop]; [by rewrite Hrew in Ha |].
  by apply Hlocal; [apply set_esatisfies_set_pattern_valuation |].
Qed.

End sec_predicates.
