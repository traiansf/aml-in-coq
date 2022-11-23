From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From AML Require Import Ensemble.
From AML Require Import Signature Pattern Structure.

Class PropositionalPatternValuation `{signature} {idomain} (F : Pattern -> Ensemble idomain) : Prop :=
{
  ppv_bot : F pBot ≡ ∅;
  ppv_impl : forall ϕ ψ, F (PImpl ϕ ψ) ≡ complement (F ϕ ∖ F ψ);
}.

Section sec_propositional_pattern_valuation_props.
  Context
    `{signature}
    (s : Structure)
    (F : Pattern -> Ensemble idomain)
    `{!PropositionalPatternValuation F}.

Lemma pattern_valuation_impl_alt_classic ϕ ψ :
  F (PImpl ϕ ψ) ≡ complement (F ϕ) ∪ F ψ.
Proof.
  by rewrite ppv_impl, difference_alt,
    complement_intersection_classic, complement_twice_classic.
Qed.

Lemma pattern_valuation_neg_classic ϕ :
  F (pNeg ϕ) ≡ complement (F ϕ).
Proof.
  unfold pNeg.
  rewrite pattern_valuation_impl_alt_classic, ppv_bot.
  by apply union_empty_r.
Qed.

Lemma pattern_valuation_top : F pTop ≡ top idomain.
Proof.
  unfold pTop; rewrite pattern_valuation_neg_classic, ppv_bot.
  by apply complement_top.
Qed.

Lemma pattern_valuation_or_classic ϕ ψ :
  F (pOr ϕ ψ) ≡ F ϕ ∪ F ψ.
Proof.
  unfold pOr; rewrite pattern_valuation_impl_alt_classic, pattern_valuation_neg_classic.
  by rewrite complement_twice_classic.
Qed.

Lemma pattern_valuation_and_classic ϕ ψ :
  F (pAnd ϕ ψ) ≡ F ϕ ∩ F ψ.
Proof.
  unfold pAnd.
  by rewrite pattern_valuation_neg_classic, pattern_valuation_or_classic,
    complement_union_classic, !pattern_valuation_neg_classic,
    !complement_twice_classic.
Qed.

Lemma pattern_valuation_iff_classic ϕ ψ :
  F (pIff ϕ ψ) ≡ complement (sym_diff (F ϕ) (F ψ)).
Proof.
  unfold pIff.
  rewrite pattern_valuation_and_classic, !pattern_valuation_impl_alt_classic.
  by unfold sym_diff; rewrite complement_union_classic, !difference_alt,
    !complement_intersection_classic, !complement_twice_classic.
Qed.

Lemma pattern_valuation_iff_alt_classic ϕ ψ :
  F (pIff ϕ ψ) ≡ F (PImpl ϕ ψ) ∩ F (PImpl ψ ϕ).
Proof. by unfold pIff; rewrite pattern_valuation_and_classic. Qed.

Lemma pattern_valuation_finite_conjunction_classic (ϕs : list Pattern) :
  F (finite_conjunction ϕs) ≡ ⋂ (map F ϕs).
Proof.
  induction ϕs; unfold finite_conjunction.
  - by unfold foldr; rewrite pattern_valuation_top.
  - rewrite map_cons, intersection_list_cons, <- IHϕs.
    by setoid_rewrite pattern_valuation_and_classic.
Qed.

Lemma pattern_valuation_finite_disjunction_classic (ϕs : list Pattern) :
  F (finite_disjunction ϕs) ≡ ⋃ (map F ϕs).
Proof.
  induction ϕs; unfold finite_disjunction; cbn; [by rewrite ppv_bot |].
  by rewrite pattern_valuation_or_classic, <- IHϕs.
Qed.

Lemma top_pattern_valuation_and_classic ϕ ψ :
  F (pAnd ϕ ψ) ≡ top idomain <-> F ϕ ≡ top idomain /\ F ψ ≡ top idomain.
Proof. by rewrite pattern_valuation_and_classic, top_intersection. Qed.

Lemma top_pattern_valuation_or_classic ϕ ψ :
  F (pOr ϕ ψ) ≡ top idomain <-> F ϕ ∪ F ψ ≡ top idomain.
Proof. by rewrite pattern_valuation_or_classic. Qed.

Lemma top_pattern_valuation_impl_classic ϕ ψ :
  F (PImpl ϕ ψ) ≡ top idomain <-> F ϕ ⊆ F ψ.
Proof.
  rewrite ppv_impl, complement_top.
  by symmetry; apply subseteq_empty_difference_classic.
Qed.

Lemma top_pattern_valuation_neg_classic ϕ :
  F (pNeg ϕ) ≡ top idomain <-> F ϕ ≡ ∅.
Proof.
  unfold pNeg; rewrite top_pattern_valuation_impl_classic, ppv_bot.
  rewrite set_equiv_subseteq; split; intro Hsub; [| by apply Hsub].
  by split; [| apply empty_subseteq].
Qed.

Lemma top_pattern_valuation_iff_classic ϕ ψ :
  F (pIff ϕ ψ) ≡ top idomain <-> F ϕ ≡ F ψ.
Proof.
  by unfold pIff; rewrite top_pattern_valuation_and_classic,
    !top_pattern_valuation_impl_classic, set_equiv_subseteq.
Qed.

Lemma top_pattern_valuation_finite_conjunction_classic (ϕs : list Pattern) :
  F (finite_conjunction ϕs) ≡ top idomain <-> Forall (fun ϕ => F ϕ ≡ top idomain) ϕs.
Proof.
  by rewrite pattern_valuation_finite_conjunction_classic, top_intersection_list, Forall_map.
Qed.

Context
  `{Set_ Pattern PatternSet}.

Definition set_propositional_pattern_valuation
  (Gamma : PatternSet) : Ensemble idomain :=
    filtered_intersection (.∈ Gamma ) F.

Lemma elem_of_set_propositional_pattern_valuation Gamma a :
  a ∈ set_propositional_pattern_valuation Gamma
    <->
  forall ϕ, ϕ ∈ Gamma -> a ∈ F ϕ.
Proof. by apply elem_of_filtered_intersection. Qed.

#[export] Instance set_propositional_pattern_valuation_proper :
  Proper ((≡) ==> (≡)) set_propositional_pattern_valuation.
Proof.
  intros Gamma Delta Heqv a; rewrite !elem_of_set_propositional_pattern_valuation.
  by setoid_rewrite Heqv.
Qed.

#[export] Instance set_propositional_pattern_valuation_proper_subseteq :
  Proper ((⊆) --> (⊆)) set_propositional_pattern_valuation.
Proof.
  intros Gamma Delta Hsub a; rewrite !elem_of_set_propositional_pattern_valuation.
  by intros HGamma ϕ Hϕ; apply HGamma, Hsub.
Qed.

Lemma set_propositional_pattern_valuation_empty_top : set_propositional_pattern_valuation ∅ ≡ top idomain.
Proof. apply filtered_intersection_empty_top, not_elem_of_empty. Qed.

Lemma set_propositional_pattern_valuation_singleton ϕ :
  set_propositional_pattern_valuation {[ϕ]} ≡ F ϕ.
Proof.
  unfold set_propositional_pattern_valuation; intro a; rewrite elem_of_filtered_intersection.
  setoid_rewrite elem_of_singleton.
  by firstorder congruence.
Qed.

Lemma top_set_propositional_pattern_valuation Gamma :
  set_propositional_pattern_valuation Gamma ≡ top idomain
    <->
  forall ϕ, ϕ ∈ Gamma -> F ϕ ≡ top idomain.
Proof.
  setoid_rewrite elem_of_equiv_top.
  setoid_rewrite elem_of_set_propositional_pattern_valuation.
  itauto.
Qed.

End sec_propositional_pattern_valuation_props.
