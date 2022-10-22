From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From AML Require Import Ensemble.
From AML Require Import Signature Pattern Structure.

Class PropositionalPatternValuation `{signature} {idomain} (F : Pattern -> Ensemble idomain) : Prop :=
{
  ppv_bot : F PBot ≡ ∅;
  ppv_impl : forall phi psi, F (PImpl phi psi) ≡ complement (F phi ∖ F psi);
}.

Section sec_propositional_pattern_valuation_props.
  Context
    `{signature}
    (s : Structure)
    (F : Pattern -> Ensemble idomain)
    `{!PropositionalPatternValuation F}.

Lemma pattern_valuation_impl_alt_classic phi psi :
  F (PImpl phi psi) ≡ complement (F phi) ∪ F psi.
Proof.
  by rewrite ppv_impl, difference_alt,
    complement_intersection_classic, complement_twice_classic.
Qed.

Lemma pattern_valuation_neg_classic phi :
  F (pNeg phi) ≡ complement (F phi).
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

Lemma pattern_valuation_or_classic phi psi :
  F (pOr phi psi) ≡ F phi ∪ F psi.
Proof.
  unfold pOr; rewrite pattern_valuation_impl_alt_classic, pattern_valuation_neg_classic.
  by rewrite complement_twice_classic.
Qed.

Lemma pattern_valuation_and_classic phi psi :
  F (pAnd phi psi) ≡ F phi ∩ F psi.
Proof.
  unfold pAnd.
  by rewrite pattern_valuation_neg_classic, pattern_valuation_or_classic,
    complement_union_classic, !pattern_valuation_neg_classic,
    !complement_twice_classic.
Qed.

Lemma pattern_valuation_iff_classic phi psi :
  F (pIff phi psi) ≡ complement (sym_diff (F phi) (F psi)).
Proof.
  unfold pIff.
  rewrite pattern_valuation_and_classic, !pattern_valuation_impl_alt_classic.
  by unfold sym_diff; rewrite complement_union_classic, !difference_alt,
    !complement_intersection_classic, !complement_twice_classic.
Qed.

Lemma pattern_valuation_iff_alt_classic phi psi :
  F (pIff phi psi) ≡ F (PImpl phi psi) ∩ F (PImpl psi phi).
Proof. by unfold pIff; rewrite pattern_valuation_and_classic. Qed.

Lemma pattern_valuation_finite_conjunction_classic (phis : list Pattern) :
  F (finite_conjunction phis) ≡ ⋂ (map F phis).
Proof.
  induction phis; unfold finite_conjunction.
  - by unfold foldr; rewrite pattern_valuation_top.
  - rewrite map_cons, intersection_list_cons, <- IHphis.
    by setoid_rewrite pattern_valuation_and_classic.
Qed.

Lemma pattern_valuation_finite_disjunction_classic (phis : list Pattern) :
  F (finite_disjunction phis) ≡ ⋃ (map F phis).
Proof.
  induction phis; unfold finite_disjunction; cbn; [by rewrite ppv_bot |].
  by rewrite pattern_valuation_or_classic, <- IHphis.
Qed.

Lemma top_pattern_valuation_and_classic phi psi :
  F (pAnd phi psi) ≡ top idomain <-> F phi ≡ top idomain /\ F psi ≡ top idomain.
Proof. by rewrite pattern_valuation_and_classic, top_intersection. Qed.

Lemma top_pattern_valuation_or_classic phi psi :
  F (pOr phi psi) ≡ top idomain <-> F phi ∪ F psi ≡ top idomain.
Proof. by rewrite pattern_valuation_or_classic. Qed.

Lemma top_pattern_valuation_impl_classic phi psi :
  F (PImpl phi psi) ≡ top idomain <-> F phi ⊆ F psi.
Proof.
  rewrite ppv_impl, complement_top.
  by symmetry; apply subseteq_empty_difference_classic.
Qed.

Lemma top_pattern_valuation_neg_classic phi :
  F (pNeg phi) ≡ top idomain <-> F phi ≡ ∅.
Proof.
  unfold pNeg; rewrite top_pattern_valuation_impl_classic, ppv_bot.
  rewrite set_equiv_subseteq; split; intro Hsub; [| by apply Hsub].
  by split; [| apply empty_subseteq].
Qed.

Lemma top_pattern_valuation_iff_classic phi psi :
  F (pIff phi psi) ≡ top idomain <-> F phi ≡ F psi.
Proof.
  by unfold pIff; rewrite top_pattern_valuation_and_classic,
    !top_pattern_valuation_impl_classic, set_equiv_subseteq.
Qed.

Lemma top_pattern_valuation_finite_conjunction_classic (phis : list Pattern) :
  F (finite_conjunction phis) ≡ top idomain <-> Forall (fun phi => F phi ≡ top idomain) phis.
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
  forall phi, phi ∈ Gamma -> a ∈ F phi.
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
  by intros HGamma phi Hphi; apply HGamma, Hsub.
Qed.

Lemma set_propositional_pattern_valuation_empty_top : set_propositional_pattern_valuation ∅ ≡ top idomain.
Proof. apply filtered_intersection_empty_top, not_elem_of_empty. Qed.

Lemma set_propositional_pattern_valuation_singleton phi :
  set_propositional_pattern_valuation {[phi]} ≡ F phi.
Proof.
  unfold set_propositional_pattern_valuation; intro a; rewrite elem_of_filtered_intersection.
  setoid_rewrite elem_of_singleton.
  by firstorder congruence.
Qed.

Lemma top_set_propositional_pattern_valuation Gamma :
  set_propositional_pattern_valuation Gamma ≡ top idomain
    <->
  forall phi, phi ∈ Gamma -> F phi ≡ top idomain.
Proof.
  setoid_rewrite elem_of_equiv_top.
  setoid_rewrite elem_of_set_propositional_pattern_valuation.
  itauto.
Qed.

End sec_propositional_pattern_valuation_props.
