From stdpp Require Import prelude.
From Coq Require Import Classical IndefiniteDescription.
From AML Require Import Functions Ensemble.
From AML Require Import Signature Pattern Variables Substitution.
From AML Require Import Structure Valuation PropositionalPatternValuation.

Section sec_pattern_valuation.

Context
  `{signature}
  (s : Structure)
  .

Definition ext_iapp (B C : Ensemble idomain) : Ensemble idomain :=
    fun x => exists b, b ∈ B /\ exists c, c ∈ C /\ x ∈ iapp b c.

Fixpoint pattern_valuation (e : Valuation) (p : Pattern) : Ensemble idomain :=
  match p with
  | PEVar x => {[eval e x]}
  | PSVar X => sval e X
  | POp o => isigma o
  | PApp ϕ ψ => ext_iapp (pattern_valuation e ϕ) (pattern_valuation e ψ)
  | PImpl ϕ ψ => complement (pattern_valuation e ϕ ∖ pattern_valuation e ψ)
  | PEx x ϕ => indexed_union (fun a => pattern_valuation (valuation_eupdate e x a) ϕ)
  | μₚ X ϕ => filtered_intersection (fun B => pattern_valuation (valuation_supdate e X B) ϕ ⊆ B) id
  end.

Lemma pattern_valuation_app e ϕ ψ :
  pattern_valuation e (PApp ϕ ψ)
    =
  ext_iapp (pattern_valuation e ϕ) (pattern_valuation e ψ).
Proof. done. Qed.

Lemma pattern_valuation_ex e x ϕ :
  pattern_valuation e (PEx x ϕ)
    =
  indexed_union (fun a => pattern_valuation (valuation_eupdate e x a) ϕ).
Proof. done. Qed.

Lemma pattern_valuation_mu e X ϕ :
  pattern_valuation e (μₚ X ϕ)
    =
  filtered_intersection  (fun B => pattern_valuation (valuation_supdate e X B) ϕ ⊆ B) id.
Proof. done. Qed.

Lemma pattern_valuation_bot e : pattern_valuation e pBot ≡ ∅.
Proof.
  cbn; intro; rewrite elem_of_filtered_intersection; split;
    [| by intro Hempty; contradict Hempty; apply not_elem_of_empty].
  by intro Hbot; apply Hbot; rewrite fn_update_eq.
Qed.

#[export] Instance propositional_pattern_valuation e :
  PropositionalPatternValuation (pattern_valuation e).
Proof. by constructor; [apply pattern_valuation_bot |]. Qed.

Section set_pattern_valuation.

Context `{Set_ Pattern PatternSet}.

Definition set_pattern_valuation  (e : Valuation) (Gamma : PatternSet) : Ensemble idomain :=
  set_propositional_pattern_valuation s (pattern_valuation e) Gamma.

Lemma elem_of_set_pattern_valuation e Gamma a :
  a ∈ set_pattern_valuation e Gamma
    <->
  forall ϕ, ϕ ∈ Gamma -> a ∈ pattern_valuation e ϕ.
Proof. by apply elem_of_set_propositional_pattern_valuation. Qed.

#[export] Instance set_pattern_valuation_proper e :
  Proper ((≡) ==> (≡)) (set_pattern_valuation e).
Proof. by apply set_propositional_pattern_valuation_proper. Qed.

#[export] Instance set_pattern_valuation_proper_subseteq e :
  Proper ((⊆) --> (⊆)) (set_pattern_valuation e).
Proof. by apply set_propositional_pattern_valuation_proper_subseteq. Qed.

Lemma set_pattern_valuation_empty_top e : set_pattern_valuation e ∅ ≡ top idomain.
Proof. by eapply set_propositional_pattern_valuation_empty_top. Qed.

Lemma set_pattern_valuation_singleton e ϕ :
  set_pattern_valuation e {[ϕ]} ≡ pattern_valuation e ϕ.
Proof. by eapply set_propositional_pattern_valuation_singleton; [typeclasses eauto |]. Qed.

Lemma top_set_pattern_valuation e Gamma :
  set_pattern_valuation e Gamma ≡ top idomain
    <->
  forall ϕ, ϕ ∈ Gamma -> pattern_valuation e ϕ ≡ top idomain.
Proof. by eapply top_set_propositional_pattern_valuation. Qed.

End set_pattern_valuation.

Lemma pattern_valuation_forall_classic e x ϕ :
  pattern_valuation e (pAll x ϕ)
    ≡
  indexed_intersection (fun a => pattern_valuation (valuation_eupdate e x a) ϕ).
Proof.
  unfold pAll; rewrite pattern_valuation_neg_classic by typeclasses eauto.
  rewrite pattern_valuation_ex, complement_indexed_union.
  intro a; rewrite !elem_of_indexed_intersection.
  apply forall_proper; intro a_x; unfold compose.
  by rewrite pattern_valuation_neg_classic, complement_twice_classic by typeclasses eauto.
Qed.

Record FV_equal (e1 e2 : Valuation) (ϕ : Pattern) : Prop :=
{
  fve_evar : forall x, EVarFree x ϕ -> eval e1 x = eval e2 x;
  fve_svar : forall X, SVarFree X ϕ -> sval e1 X ≡ sval e2 X;
}.

Lemma FV_equal_equiv e1 e2 ϕ : e1 ≡ e2 -> FV_equal e1 e2 ϕ.
Proof.
  intros []; split; intros; [apply veqve | apply veqvs].
Qed.

Lemma elem_of_ext_iapp a B C :
  a ∈ ext_iapp B C <-> exists b, b ∈ B /\ exists c, c ∈ C /\ a ∈ iapp b c.
Proof. done. Qed.

Lemma ext_iapp_empty_r : forall B, ext_iapp B ∅ ≡ ∅.
Proof.
  intros B; apply elem_of_equiv_empty.
  intros x (_ & _ & c & Hc & _); contradict Hc; eapply not_elem_of_empty.
Qed.

Lemma ext_iapp_empty_l : forall B, ext_iapp ∅ B ≡ ∅.
Proof.
  intros B; apply elem_of_equiv_empty.
  intros x (c & Hc & _); contradict Hc; eapply not_elem_of_empty.
Qed.

Lemma ext_iapp_union_l C D B :
  ext_iapp (C ∪ D) B ≡ ext_iapp C B ∪ ext_iapp D B.
Proof.
  intro a; rewrite elem_of_union; split.
  - intros (cd & Hcd & b & Hb & Ha); rewrite elem_of_union in Hcd.
    by destruct Hcd as [Hc | Hd]; [left | right]; repeat esplit.
  - intros [(c & Hc & b & Hb & Ha) | (d & Hd & b & Hb & Ha)];
      eexists; rewrite elem_of_union; split; [by left | | by right |];
      by repeat esplit.
Qed.

Lemma ext_iapp_union_r C D B :
  ext_iapp B (C ∪ D) ≡ ext_iapp B C ∪ ext_iapp B D.
Proof.
  intro a; rewrite elem_of_union; split.
  - intros (b & Hb & cd & Hcd & Ha); rewrite elem_of_union in Hcd.
    by destruct Hcd as [Hc | Hd]; [left | right]; repeat esplit.
  - intros [(b & Hb & c & Hc & Ha) | (b & Hb & d & Hd & Ha)];
      eexists; (split; [done |]); eexists; rewrite elem_of_union;
      split; [by left | | by right |];
      by repeat esplit.
Qed.

Lemma ext_iapp_intersection_l C D B :
  ext_iapp (C ∩ D) B ⊆ ext_iapp C B ∩ ext_iapp D B.
Proof.
  intro a; rewrite elem_of_intersection.
  intros (cd & Hcd & b & Hb & Ha); rewrite elem_of_intersection in Hcd.
  by destruct Hcd as [Hc Hd]; repeat esplit.
Qed.

Lemma ext_iapp_intersection_r C D B :
  ext_iapp B (C ∩ D) ⊆ ext_iapp B C ∩ ext_iapp B D.
Proof.
  intro a; rewrite elem_of_intersection.
  intros (b & Hb & cd & Hcd & Ha); rewrite elem_of_intersection in Hcd.
  by destruct Hcd as [Hc Hd]; repeat esplit.
Qed.

Lemma ext_iapp_filtered_union_l `(P : index -> Prop) (A : index -> Ensemble idomain) B :
  ext_iapp (filtered_union P A) B ≡ filtered_union P (fun i => ext_iapp (A i) B).
Proof.
  split.
  - by intros (a & (i & Hi & Ha) & b & Hb & Hx); repeat esplit.
  - by intros (i & Hi & ai & Hai & b & Hb & Hx); repeat esplit.
Qed.

Lemma ext_iapp_indexed_union_l `(A : index -> Ensemble idomain) B :
  ext_iapp (indexed_union A) B ≡ indexed_union (fun i => ext_iapp (A i) B).
Proof. by apply ext_iapp_filtered_union_l. Qed.

Lemma ext_iapp_filtered_union_r `(P : index -> Prop) (A : index -> Ensemble idomain) B :
  ext_iapp B (filtered_union P A) ≡ filtered_union P (fun i => ext_iapp B (A i)).
Proof.
  split.
  - by intros (b & Hb & a & (i & Hi & Ha) & Hx); repeat esplit.
  - by intros (i & b & Hb & Hi & ai & Hai & Hx); repeat esplit.
Qed.
Lemma ext_iapp_indexed_union_r `(A : index -> Ensemble idomain) B :
  ext_iapp B (indexed_union A) ≡ indexed_union (fun i => ext_iapp B (A i)).
Proof. by apply ext_iapp_filtered_union_r. Qed.

Lemma ext_iapp_filtered_intersection_l `(P : index -> Prop) (A : index -> Ensemble idomain) B :
  ext_iapp (filtered_intersection P A) B ⊆ filtered_intersection P (fun i => ext_iapp (A i) B).
Proof.
  intros x (a & Ha & b & Hb & Hx) i Hi.
  by exists a; split; [apply Ha | repeat esplit].
Qed.

Lemma ext_iapp_indexed_intersection_l `(A : index -> Ensemble idomain) B :
  ext_iapp (indexed_intersection A) B ⊆ indexed_intersection (fun i => ext_iapp (A i) B).
Proof. by apply ext_iapp_filtered_intersection_l. Qed.

Lemma ext_iapp_filtered_intersection_r `(P : index -> Prop) (A : index -> Ensemble idomain) B :
  ext_iapp B (filtered_intersection P A) ⊆ filtered_intersection P (fun i => ext_iapp B (A i)).
Proof.
  intros x (b & Hb & a & Ha & Hx) i Hi.
  exists b; split; [done |].
  by exists a; split; [apply Ha |].
Qed.

Lemma ext_iapp_indexed_intersection_r `(A : index -> Ensemble idomain) B :
  ext_iapp B (indexed_intersection A) ⊆ indexed_intersection (fun i => ext_iapp B (A i)).
Proof. by apply ext_iapp_filtered_intersection_r. Qed.

#[export] Instance ext_iapp_Proper_subseteq_l : Proper ((⊆) ==> (≡) ==> (⊆)) ext_iapp.
Proof.
  intros B C Hbc D E Hde.
  intros a (b & Hb & d & Hd & Ha).
  by exists b; split; [apply Hbc | exists d; split; [apply Hde |]].
Qed.

#[export] Instance ext_iapp_Proper_subseteq_r : Proper ((≡) ==> (⊆) ==> (⊆)) ext_iapp.
Proof.
  intros B C Hbc D E Hde.
  intros a (b & Hb & d & Hd & Ha).
  by exists b; split; [apply Hbc | exists d; split; [apply Hde |]].
Qed.

#[export] Instance ext_iapp_Proper_subseteq : Proper ((⊆) ==> (⊆) ==> (⊆)) ext_iapp.
Proof.
  intros B C Hbc D E Hde.
  by transitivity (ext_iapp B E); [rewrite Hde | rewrite Hbc].
Qed.

#[export] Instance ext_iapp_Proper : Proper ((≡) ==> (≡) ==> (≡)) ext_iapp.
Proof.
  intros B C Hbc D E Hde a; rewrite ! elem_of_ext_iapp.
  by setoid_rewrite Hbc; setoid_rewrite Hde.
Qed.

Lemma ext_iapp_complement_l B C D (Hbc : B ⊆ C) :
  ext_iapp (complement C) D ⊆ ext_iapp (complement B) D.
Proof.
  by eapply complement_subseteq_proper in Hbc; cbn in Hbc; rewrite Hbc.
Qed.

Lemma ext_iapp_complement_r B C D (Hbc : B ⊆ C) :
  ext_iapp D (complement C) ⊆ ext_iapp D (complement B).
Proof.
  by eapply complement_subseteq_proper in Hbc; cbn in Hbc; rewrite Hbc.
Qed.

Lemma pattern_valuation_fv ϕ :
  forall e1 e2, FV_equal e1 e2 ϕ ->
    pattern_valuation e1 ϕ ≡ pattern_valuation e2 ϕ.
Proof.
  induction ϕ; cbn; intros e1 e2 [].
  - by rewrite fve_evar0; [| constructor].
  - by rewrite fve_svar0; [| constructor].
  - rewrite IHϕ1, IHϕ2; [done |..]; split; intros.
    + by apply fve_evar0, ef_impl_right.
    + by apply fve_svar0, sf_impl_right.
    + by apply fve_evar0, ef_impl_left.
    + by apply fve_svar0, sf_impl_left.
  - intro b; rewrite !elem_of_indexed_union.
    cut (forall i : idomain, pattern_valuation (valuation_eupdate e1 e i) ϕ
      ≡ pattern_valuation (valuation_eupdate e2 e i) ϕ);
      [by intro Hrew; setoid_rewrite Hrew |].
    intro a; rewrite IHϕ; [done |].
    split; intros x Hx.
    + cbn; unfold fn_update; case_decide; [done |].
      by apply fve_evar0; constructor.
    + by apply fve_svar0; constructor.
  - intro a; rewrite !elem_of_filtered_intersection.
    apply forall_proper; intro A.
    rewrite IHϕ; [done |].
    split; intros x Hx.
    + by apply fve_evar0; constructor.
    + cbn; unfold fn_update; case_decide; [done |].
      by apply fve_svar0; constructor.
  - intro a; rewrite !elem_of_ext_iapp.
    setoid_rewrite (IHϕ1 e1 e2); [setoid_rewrite (IHϕ2 e1 e2) |]; [done |..];
      split; intros.
    + by apply fve_evar0, ef_app_right.
    + by apply fve_svar0, sf_app_right.
    + by apply fve_evar0, ef_app_left.
    + by apply fve_svar0, sf_app_left.
  - done.
Qed.

Lemma pattern_valuation_eupdate_not_free e x a ϕ :
  ~ EVarFree x ϕ ->
  pattern_valuation (valuation_eupdate e x a) ϕ
    ≡
  pattern_valuation e ϕ.
Proof.
  intro Hx.
  apply pattern_valuation_fv; split; [cbn | done].
  by intros; unfold fn_update; case_decide; subst.
Qed.

Lemma pattern_valuation_supdate_not_free e x a ϕ :
  ~ SVarFree x ϕ ->
  pattern_valuation (valuation_supdate e x a) ϕ
    ≡
  pattern_valuation e ϕ.
Proof.
  intro Hx.
  apply pattern_valuation_fv; split; [done | cbn].
  by intros; unfold fn_update; case_decide; subst.
Qed.

Lemma ClosedPattern_FV_equal (ϕ : Pattern) (e1 e2 : Valuation) :
  ClosedPattern ϕ -> FV_equal e1 e2 ϕ.
Proof. intros []; split; intros x Hx; contradict Hx; done. Qed.

Lemma pattern_valuation_closed_pattern e1 e2 ϕ :
  ClosedPattern ϕ -> pattern_valuation e1 ϕ ≡ pattern_valuation e2 ϕ.
Proof. by intro; apply pattern_valuation_fv, ClosedPattern_FV_equal. Qed.

Instance pattern_valuation_proper : Proper ((≡) ==> (=) ==> (≡)) pattern_valuation.
Proof.
  intros e1 e2 [] _ϕ ϕ ->.
  induction ϕ.
  - by cbn; rewrite veqve.
  - by cbn; rewrite veqvs.
  - by cbn; rewrite IHϕ1, IHϕ2.
  - cbn; intro a; rewrite! elem_of_indexed_union.
    apply exist_proper; intro b.
    by apply pattern_valuation_fv, FV_equal_equiv, valuation_eupdate_proper; [split |..].
  - cbn; intro a; rewrite! elem_of_filtered_intersection.
    apply forall_proper; intro A.
    cut (pattern_valuation (valuation_supdate e1 s0 A) ϕ ≡ pattern_valuation (valuation_supdate e2 s0 A) ϕ);
      [by intros -> |].
    by apply pattern_valuation_fv, FV_equal_equiv, valuation_supdate_proper; [split |..].
  - by cbn; rewrite IHϕ1, IHϕ2.
  - done.
Qed.

Definition evaluates_to_singleton (e : Valuation) (ϕ : Pattern) : Prop :=
  exists a, pattern_valuation e ϕ ≡ {[a]}.

Class always_evaluates_to_singleton (ϕ : Pattern) : Prop :=
{
  aes : forall (e : Valuation), evaluates_to_singleton e ϕ
}.

#[export] Instance always_evaluates_to_singleton_evar x :
  always_evaluates_to_singleton (PEVar x).
Proof. by constructor; intros; eexists. Qed.

Definition singleton_value
  (ϕ : Pattern) `{!always_evaluates_to_singleton ϕ}
  (e : Valuation) : { a : idomain | pattern_valuation e ϕ ≡ {[a]} }.
Proof.
  destruct always_evaluates_to_singleton0.
  specialize (aes0 e).
  by apply constructive_indefinite_description in aes0.
Qed.

Lemma pattern_valuation_evar_sub0_not_free e x delta ϕ c :
  ~ EVarFree x ϕ ->
  pattern_valuation e (evar_sub0 x delta ϕ)
    ≡
  pattern_valuation (valuation_eupdate e x c) ϕ.
Proof.
  intro; erewrite evar_sub0_not_free by done.
  apply pattern_valuation_fv; split; [| done].
  intros y Hy; cbn; unfold fn_update.
  by case_decide; subst.
Qed.

Lemma pattern_valuation_evar_sub0 e x delta ϕ
  `{!always_evaluates_to_singleton delta} :
  EFreeFor x delta ϕ ->
  pattern_valuation e (evar_sub0 x delta ϕ)
    ≡
  pattern_valuation (valuation_eupdate e x (` (singleton_value delta e))) ϕ.
Proof.
  remember (proj1_sig _) as c.
  intros Hfree_for.
  destruct (classic (EVarFree x ϕ)) as [Hfree |];
    [| by apply pattern_valuation_evar_sub0_not_free].
  revert e c Heqc; induction ϕ; try (by inversion Hfree); intros ? c Hc.
  - by inversion Hfree; subst; cbn; unfold fn_update;
      rewrite !decide_True by done; destruct singleton_value.
  - rewrite pattern_valuation_impl_alt_classic by typeclasses eauto.
    apply EFreeForImpl in Hfree_for as [Hfree_for1 Hfree_for2].
    destruct (classic (EVarFree x ϕ1)); [destruct (classic (EVarFree x ϕ2)) |].
    + rewrite <- IHϕ1, <- IHϕ2 by done.
      apply pattern_valuation_impl_alt_classic; typeclasses eauto.
    + rewrite <- IHϕ1, <- pattern_valuation_evar_sub0_not_free
        with (ϕ := ϕ2) (delta := delta) by done.
      apply pattern_valuation_impl_alt_classic; typeclasses eauto.
    + inversion Hfree; [done | subst].
      rewrite <- IHϕ2, <- pattern_valuation_evar_sub0_not_free
        with (ϕ := ϕ1) (delta := delta) by done.
      apply pattern_valuation_impl_alt_classic; typeclasses eauto.
  - apply EFreeForEx in Hfree_for as [Hfree_for1 Hx].
    inversion Hfree; subst y ϕ0.
    cbn; rewrite decide_False by done; cbn.
    intro a; rewrite !elem_of_indexed_union.
    setoid_rewrite IHϕ; [| done..].
    apply exist_proper; intro b.
    rewrite valuation_eupdate_comm by done.
    subst; destruct (singleton_value delta e0) as [c Hc].
    destruct (singleton_value delta (valuation_eupdate e0 e b)) as [d Hd]; cbn.
    rewrite pattern_valuation_fv, Hc in Hd;
      [by apply singleton_equiv_inj in Hd; subst |].
    split; cbn; [| done]; intros; unfold fn_update.
    case_decide; [| done].
    by subst; exfalso; apply Hx.
  - apply EFreeForMu in Hfree_for as [Hfree_for1 Hx].
    inversion Hfree; subst; cbn.
    intro a; rewrite !elem_of_filtered_intersection.
    setoid_rewrite IHϕ; [| done..].
    setoid_rewrite valuation_esupdate_comm.
    apply forall_proper; intro A.
    destruct (singleton_value delta e) as [c Hc].
    destruct (singleton_value delta (valuation_supdate e s0 A)) as [d Hd]; cbn.
    rewrite pattern_valuation_fv, Hc in Hd;
      [by apply singleton_equiv_inj in Hd; subst |].
    split; cbn; [done |]; intros; unfold fn_update.
    case_decide; [| done].
    by subst; exfalso; apply Hx.
  - cbn.
    apply EFreeForApp in Hfree_for as [Hfree_for1 Hfree_for2].
    destruct (classic (EVarFree x ϕ1)); [destruct (classic (EVarFree x ϕ2)) |].
    + by rewrite <- IHϕ1, <- IHϕ2.
    + by rewrite <- IHϕ1, <- pattern_valuation_evar_sub0_not_free
        with (ϕ := ϕ2) (delta := delta).
    + inversion Hfree; [done | subst].
      by rewrite <- IHϕ2, <- pattern_valuation_evar_sub0_not_free
        with (ϕ := ϕ1) (delta := delta).
Qed.

Lemma pattern_valuation_evar_sub0_evar e x y ϕ :
  EFreeFor x (PEVar y) ϕ ->
  pattern_valuation e (evar_sub0 x (PEVar y) ϕ)
    ≡
  pattern_valuation (valuation_eupdate e x (eval e y)) ϕ.
Proof.
  intro Hfree_for.
  unshelve rewrite pattern_valuation_evar_sub0 by done;
    [typeclasses eauto |].
  destruct (singleton_value (PEVar y) e); cbn in *.
  by apply singleton_equiv_inj in e0 as <-.
Qed.

Lemma pattern_valuation_svar_sub0_not_free e x delta ϕ c :
  ~ SVarFree x ϕ ->
  pattern_valuation e (svar_sub0 x delta ϕ)
    ≡
  pattern_valuation (valuation_supdate e x c) ϕ.
Proof.
  intro; erewrite svar_sub0_not_free by done.
  apply pattern_valuation_fv; split; [done |].
  intros y Hy; cbn; unfold fn_update.
  by case_decide; subst.
Qed.

Lemma pattern_valuation_svar_sub0 e x delta ϕ :
  SFreeFor x delta ϕ ->
  pattern_valuation e (svar_sub0 x delta ϕ)
    ≡
  pattern_valuation (valuation_supdate e x (pattern_valuation e delta)) ϕ.
Proof.
  intros Hfree_for.
  destruct (classic (SVarFree x ϕ)) as [Hfree |];
    [| by apply pattern_valuation_svar_sub0_not_free].
  revert e; induction ϕ; try (by inversion Hfree); intros ?.
  - by inversion Hfree; subst; cbn; unfold fn_update;
      rewrite !decide_True by done.
  - rewrite pattern_valuation_impl_alt_classic by typeclasses eauto.
    apply SFreeForImpl in Hfree_for as [Hfree_for1 Hfree_for2].
    destruct (classic (SVarFree x ϕ1)); [destruct (classic (SVarFree x ϕ2)) |].
    + rewrite <- IHϕ1, <- IHϕ2 by done.
      apply pattern_valuation_impl_alt_classic; typeclasses eauto.
    + rewrite <- IHϕ1, <- pattern_valuation_svar_sub0_not_free
        with (ϕ := ϕ2) (delta := delta) by done.
      apply pattern_valuation_impl_alt_classic; typeclasses eauto.
    + inversion Hfree; [done | subst].
      rewrite <- IHϕ2, <- pattern_valuation_svar_sub0_not_free
        with (ϕ := ϕ1) (delta := delta) by done.
      apply pattern_valuation_impl_alt_classic; typeclasses eauto.
  - apply SFreeForEx in Hfree_for as [Hfree_for1 Hx].
    inversion Hfree; subst X ϕ0.
    cbn.
    intro a; rewrite !elem_of_indexed_union.
    setoid_rewrite IHϕ; [| done..].
    apply exist_proper; intro b.
    rewrite valuation_esupdate_comm by done.
    apply pattern_valuation_proper; [| done].
    apply valuation_eupdate_proper; [| done..].
    apply valuation_supdate_proper; [done..|].
    apply pattern_valuation_eupdate_not_free.
    by intro; apply Hx.
  - apply SFreeForMu in Hfree_for as [Hfree_for1 Hx].
    inversion Hfree; subst; cbn; rewrite decide_False by done; cbn.
    intro a; rewrite !elem_of_filtered_intersection.
    setoid_rewrite IHϕ; [| done..].
    apply forall_proper; intro A.
    rewrite valuation_supdate_comm by done.
    cut
      (pattern_valuation
        (valuation_supdate
          (valuation_supdate e x
            (pattern_valuation (valuation_supdate e s0 A) delta)) s0 A) ϕ
        ≡
      pattern_valuation
        (valuation_supdate (valuation_supdate e x (pattern_valuation e delta))
          s0 A) ϕ);
      [by intros -> |].
    apply pattern_valuation_proper; [| done].
    apply valuation_supdate_proper; [| done..].
    apply valuation_supdate_proper; [done.. |].
    apply pattern_valuation_supdate_not_free.
    by intro; apply Hx.
  - cbn.
    apply SFreeForApp in Hfree_for as [Hfree_for1 Hfree_for2].
    destruct (classic (SVarFree x ϕ1)); [destruct (classic (SVarFree x ϕ2)) |].
    + by rewrite <- IHϕ1, <- IHϕ2.
    + by rewrite <- IHϕ1, <- pattern_valuation_svar_sub0_not_free
        with (ϕ := ϕ2) (delta := delta).
    + inversion Hfree; [done | subst].
      by rewrite <- IHϕ2, <- pattern_valuation_svar_sub0_not_free
        with (ϕ := ϕ1) (delta := delta).
Qed.

Lemma pattern_valuation_svar_sub0_svar e x y ϕ :
  SFreeFor x (PSVar y) ϕ ->
  pattern_valuation e (svar_sub0 x (PSVar y) ϕ)
    ≡
  pattern_valuation (valuation_supdate e x (sval e y)) ϕ.
Proof.
  by intro Hfree_for; rewrite pattern_valuation_svar_sub0.
Qed.

Lemma pattern_valuation_nu_classic e X ϕ :
  pattern_valuation e (νₚ X ϕ)
    ≡
  filtered_union (fun B => B ⊆ pattern_valuation (valuation_supdate e X B) ϕ) id.
Proof.
  unfold νₚ.
  rewrite pattern_valuation_neg_classic, pattern_valuation_mu by typeclasses eauto.
  rewrite complement_filtered_intersection_classic.
  assert (Hfree_for : SFreeFor X (pNeg (PSVar X)) ϕ).
  {
    by apply SFreeFor_x_theta_if_no_free_vars; cbn; set_solver.
  }
  intro x; rewrite !elem_of_filtered_union.
  split; intros (A & HA & Hx).
  - rewrite pattern_valuation_neg_classic in HA by typeclasses eauto.
    rewrite pattern_valuation_svar_sub0, valuation_supdate_twice in HA by done.
    apply complement_subseteq_proper in HA; rewrite complement_twice_classic in HA.
    exists (complement A); split; [| done].
    etransitivity; [done |].
    apply set_equiv_subseteq, pattern_valuation_proper; [| done].
    apply valuation_supdate_proper; [done.. |].
    rewrite pattern_valuation_neg_classic by typeclasses eauto.
    by cbn; rewrite fn_update_eq.
  - exists (complement A); split; [| by cbn; rewrite complement_twice_classic].
    apply complement_subseteq_proper in HA.
    etransitivity; [| done].
    apply set_equiv_subseteq.
    rewrite pattern_valuation_neg_classic by typeclasses eauto.
    rewrite pattern_valuation_svar_sub0, valuation_supdate_twice by done.
    apply complement_equiv_proper, pattern_valuation_proper; [| done].
    apply valuation_supdate_proper; [done.. |].
    rewrite pattern_valuation_neg_classic by typeclasses eauto.
    by cbn; rewrite fn_update_eq, complement_twice_classic.
Qed.

Lemma pattern_valuation_positive_negative_proper e X ϕ A B :
  A ⊆ B ->
  (OccursPositively X ϕ ->
  pattern_valuation (valuation_supdate e X A) ϕ
    ⊆
  pattern_valuation (valuation_supdate e X B) ϕ)
  /\
  (OccursNegatively X ϕ ->
  pattern_valuation (valuation_supdate e X B) ϕ
    ⊆
  pattern_valuation (valuation_supdate e X A) ϕ).
Proof.
  intros Hincl; revert e; induction ϕ; try done; intro; split.
  - by cbn; unfold fn_update; case_decide.
  - by inversion 1; cbn; unfold fn_update; rewrite !decide_False.
  - inversion 1 as [| | | | | | | ? ? Hϕ1 Hϕ2]; subst.
    specialize (IHϕ1 e) as [_ IHϕ1].
    specialize (IHϕ2 e) as [IHϕ2 _].
    specialize (IHϕ1 Hϕ1). specialize (IHϕ2 Hϕ2).
    rewrite !pattern_valuation_impl_alt_classic by typeclasses eauto.
    intro a; rewrite !elem_of_union, !elem_of_complement.
    by set_solver.
  - inversion 1 as [| | | | | | | ? ? Hϕ1 Hϕ2]; subst.
    specialize (IHϕ1 e) as [IHϕ1 _].
    specialize (IHϕ2 e) as [_ IHϕ2].
    specialize (IHϕ1 Hϕ1). specialize (IHϕ2 Hϕ2).
    rewrite !pattern_valuation_impl_alt_classic by typeclasses eauto.
    intro a; rewrite !elem_of_union, !elem_of_complement.
    by set_solver.
  - inversion 1; subst; cbn.
    intro a; rewrite !elem_of_indexed_union.
    intros [b Hb]; exists b.
    rewrite <- valuation_esupdate_comm in Hb |- *.
    by apply IHϕ.
  - inversion 1; subst; cbn.
    intro a; rewrite !elem_of_indexed_union.
    intros [b Hb]; exists b.
    rewrite <- valuation_esupdate_comm in Hb |- *.
    by apply IHϕ.
  - inversion 1; subst; cbn; intro a; rewrite !elem_of_filtered_intersection;
      intros HA C HC; apply HA; [by rewrite valuation_supdate_twice in HC |- * |].
    rewrite valuation_supdate_comm in HC |- * by done.
    etransitivity; [| done].
    by apply IHϕ.
  - inversion 1; subst; cbn; intro a; rewrite !elem_of_filtered_intersection;
      intros HA C HC; apply HA; [by rewrite valuation_supdate_twice in HC |- * |].
    rewrite valuation_supdate_comm in HC |- * by done.
    etransitivity; [| done].
    by apply IHϕ.
  - inversion 1 as [| | | ? ? Hϕ1 Hϕ2 | | | |]; subst.
    specialize (IHϕ1 e) as [IHϕ1 _].
    specialize (IHϕ2 e) as [IHϕ2 _].
    specialize (IHϕ1 Hϕ1). specialize (IHϕ2 Hϕ2).
    by cbn; rewrite IHϕ1, IHϕ2.
  - inversion 1 as [| | | ? ? Hϕ1 Hϕ2 | | | |]; subst.
    specialize (IHϕ1 e) as [_ IHϕ1].
    specialize (IHϕ2 e) as [_ IHϕ2].
    specialize (IHϕ1 Hϕ1). specialize (IHϕ2 Hϕ2).
    by cbn; rewrite IHϕ1, IHϕ2.
Qed.

Definition pattern_valuation_fn e ϕ x a :=
  pattern_valuation (valuation_eupdate e x a) ϕ.

Definition pattern_valuation_functor e ϕ X A :=
  pattern_valuation (valuation_supdate e X A) ϕ.

Lemma pattern_valuation_functor_and e ϕ ψ X A :
  pattern_valuation_functor e (ϕ ∧ₚ ψ) X A
    ≡
  pattern_valuation_functor e ϕ X A
    ∩
  pattern_valuation_functor e ψ X A.
Proof.
  unfold pattern_valuation_functor.
  by apply pattern_valuation_and_classic; typeclasses eauto.
Qed.

Lemma pattern_valuation_functor_or e ϕ ψ X A :
  pattern_valuation_functor e (ϕ ∨ₚ ψ) X A
    ≡
  pattern_valuation_functor e ϕ X A
    ∪
  pattern_valuation_functor e ψ X A.
Proof.
  unfold pattern_valuation_functor.
  by apply pattern_valuation_or_classic; typeclasses eauto.
Qed.

Lemma pattern_valuation_functor_free e ϕ X A :
  X ∉ FSV ϕ ->
  pattern_valuation_functor e ϕ X A
    ≡
  pattern_valuation e ϕ.
Proof.
  intros HX; apply pattern_valuation_fv.
  split; intros; [done |].
  rewrite <- SVarFree_FSV in HX.
  cbn; unfold fn_update.
  by case_decide; [subst |].
Qed.

Lemma pattern_valuation_functor_neg e ϕ X A :
  pattern_valuation_functor e (¬ₚ ϕ) X A
    ≡
  complement (pattern_valuation_functor e ϕ X A).
Proof.
  unfold pattern_valuation_functor.
  by apply pattern_valuation_neg_classic; typeclasses eauto.
Qed.

Lemma pattern_valuation_functor_top e X A :
  pattern_valuation_functor e pTop X A ≡ top idomain.
Proof.
  by rewrite pattern_valuation_functor_free, pattern_valuation_top;
    [| typeclasses eauto | cbn; set_solver].
Qed.

Lemma pattern_valuation_functor_app e ϕ ψ X A :
  pattern_valuation_functor e (PApp ϕ ψ) X A
    ≡
  ext_iapp
    (pattern_valuation_functor e ϕ X A)
    (pattern_valuation_functor e ψ X A).
Proof. done. Qed.

Lemma pattern_valuation_positive_proper e ϕ X :
  OccursPositively X ϕ ->
  Proper ((⊆) ==> (⊆)) (pattern_valuation_functor e ϕ X).
Proof.
  by intros Hpos A B Hincl; revert Hpos; apply pattern_valuation_positive_negative_proper.
Qed.

Lemma pattern_valuation_negative_proper e ϕ X :
  OccursNegatively X ϕ ->
  Proper ((⊆) --> (⊆)) (pattern_valuation_functor e ϕ X).
Proof.
  by intros Hneg A B Hincl; revert Hneg; apply pattern_valuation_positive_negative_proper.
Qed.

Lemma pattern_valuation_mu_unroll ϕ X e :
  OccursPositively X ϕ ->
  pattern_valuation e (μₚ X ϕ) ≡
  pattern_valuation (valuation_supdate e X (pattern_valuation e (μₚ X ϕ))) ϕ.
Proof.
  intros Hocc.
  pose proof (pattern_valuation_positive_proper e ϕ X Hocc).
  symmetry; apply (knaster_tarsky_lfp_fix (pattern_valuation_functor e ϕ X)).
Qed.

Lemma pattern_valuation_mu_lfp ϕ X e B :
  OccursPositively X ϕ ->
  pattern_valuation (valuation_supdate e X B) ϕ ≡ B ->
  pattern_valuation e (μₚ X ϕ) ⊆ B.
Proof.
  intros Hocc Hfix.
  pose proof (pattern_valuation_positive_proper e ϕ X Hocc).
  by apply (knaster_tarsky_lfp_least (pattern_valuation_functor e ϕ X)).
Qed.

Lemma pattern_valuation_nu_unroll ϕ X e :
  OccursPositively X ϕ ->
  pattern_valuation e (νₚ X ϕ) ≡
  pattern_valuation (valuation_supdate e X (pattern_valuation e (νₚ X ϕ))) ϕ.
Proof.
  intros Hocc.
  pose proof (pattern_valuation_positive_proper e ϕ X Hocc).
  rewrite pattern_valuation_nu_classic at 1.
  specialize (knaster_tarsky_gfp_fix (pattern_valuation_functor e ϕ X)) as Hgfp.
  unfold fixpoint, gfp, pattern_valuation_functor, post_fixpoint in Hgfp; cbn in Hgfp.
  rewrite <- Hgfp.
  apply pattern_valuation_proper; [| done].
  apply valuation_supdate_proper; [done.. |].
  by rewrite pattern_valuation_nu_classic.
Qed.

Lemma pattern_valuation_nu_gfp ϕ X e B :
  OccursPositively X ϕ ->
  pattern_valuation (valuation_supdate e X B) ϕ ≡ B ->
  B ⊆ pattern_valuation e (νₚ X ϕ).
Proof.
  intros Hocc Hfix.
  pose proof (pattern_valuation_positive_proper e ϕ X Hocc).
  rewrite pattern_valuation_nu_classic.
  by apply (knaster_tarsky_gfp_greatest (pattern_valuation_functor e ϕ X)).
Qed.

Lemma pattern_valuation_context_hole e ϕ :
  pattern_valuation e (csubst Hole ϕ) = pattern_valuation e ϕ.
Proof. done. Qed.

Lemma pattern_valuation_context_l e c ϕ ψ :
  pattern_valuation e (csubst (LApp c ψ) ϕ)
   =
  ext_iapp (pattern_valuation e (csubst c ϕ)) (pattern_valuation e ψ).
Proof. done. Qed.

Lemma pattern_valuation_context_r e c ϕ ψ :
  pattern_valuation e (csubst (RApp ψ c) ϕ)
   =
  ext_iapp (pattern_valuation e ψ) (pattern_valuation e (csubst c ϕ)).
Proof. done. Qed.

End sec_pattern_valuation.
