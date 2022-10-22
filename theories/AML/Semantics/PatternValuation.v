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
  | PBot => ∅
  | PApp phi psi => ext_iapp (pattern_valuation e phi) (pattern_valuation e psi)
  | PImpl phi psi => complement (pattern_valuation e phi ∖ pattern_valuation e psi)
  | PEx x phi => indexed_union (fun a => pattern_valuation (valuation_eupdate e x a) phi)
  | PMu X phi => filtered_intersection (fun B => pattern_valuation (valuation_supdate e X B) phi ⊆ B) id
  end.

#[export] Instance propositional_pattern_valuation e :
  PropositionalPatternValuation (pattern_valuation e).
Proof. by constructor. Qed.

Section set_pattern_valuation.

Context `{Set_ Pattern PatternSet}.

Definition set_pattern_valuation  (e : Valuation) (Gamma : PatternSet) : Ensemble idomain :=
  set_propositional_pattern_valuation s (pattern_valuation e) Gamma.

Lemma elem_of_set_pattern_valuation e Gamma a :
  a ∈ set_pattern_valuation e Gamma
    <->
  forall phi, phi ∈ Gamma -> a ∈ pattern_valuation e phi.
Proof. by apply elem_of_set_propositional_pattern_valuation. Qed.

#[export] Instance set_pattern_valuation_proper e :
  Proper ((≡) ==> (≡)) (set_pattern_valuation e).
Proof. by apply set_propositional_pattern_valuation_proper. Qed.

#[export] Instance set_pattern_valuation_proper_subseteq e :
  Proper ((⊆) --> (⊆)) (set_pattern_valuation e).
Proof. by apply set_propositional_pattern_valuation_proper_subseteq. Qed.

Lemma set_pattern_valuation_empty_top e : set_pattern_valuation e ∅ ≡ top idomain.
Proof. by eapply set_propositional_pattern_valuation_empty_top. Qed.

Lemma set_pattern_valuation_singleton e phi :
  set_pattern_valuation e {[phi]} ≡ pattern_valuation e phi.
Proof. by eapply set_propositional_pattern_valuation_singleton. Qed.

Lemma top_set_pattern_valuation e Gamma :
  set_pattern_valuation e Gamma ≡ top idomain
    <->
  forall phi, phi ∈ Gamma -> pattern_valuation e phi ≡ top idomain.
Proof. by eapply top_set_propositional_pattern_valuation. Qed.

End set_pattern_valuation.

Lemma pattern_valuation_forall_classic e x phi :
  pattern_valuation e (pAll x phi)
    ≡
  indexed_intersection (fun a => pattern_valuation (valuation_eupdate e x a) phi).
Proof.
  unfold pAll; rewrite pattern_valuation_neg_classic by done; cbn.
  rewrite complement_indexed_union.
  intro a; rewrite !elem_of_indexed_intersection; cbn.
  apply forall_proper; intro a_x; rewrite complement_twice_classic, elem_of_difference.
  by split; [intros [] | intro; split; [| apply not_elem_of_empty]].
Qed.

Record FV_equal (e1 e2 : Valuation) (phi : Pattern) : Prop :=
{
  fve_evar : forall x, EVarFree x phi -> eval e1 x = eval e2 x;
  fve_svar : forall X, SVarFree X phi -> sval e1 X = sval e2 X;
}.

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

Lemma pattern_valuation_fv phi :
  forall e1 e2, FV_equal e1 e2 phi ->
    pattern_valuation e1 phi ≡ pattern_valuation e2 phi.
Proof.
  induction phi; cbn; intros e1 e2 [].
  - by rewrite fve_evar0; [| constructor].
  - by rewrite fve_svar0; [| constructor].
  - done.
  - rewrite IHphi1, IHphi2; [done |..]; split; intros.
    + by apply fve_evar0, ef_impl_right.
    + by apply fve_svar0, sf_impl_right.
    + by apply fve_evar0, ef_impl_left.
    + by apply fve_svar0, sf_impl_left.
  - intro b; rewrite !elem_of_indexed_union.
    cut (forall i : idomain, pattern_valuation (valuation_eupdate e1 e i) phi
      ≡ pattern_valuation (valuation_eupdate e2 e i) phi);
      [by intro Hrew; setoid_rewrite Hrew |].
    intro a; rewrite IHphi; [done |].
    split; intros x Hx.
    + cbn; unfold fn_update; case_decide; [done |].
      by apply fve_evar0; constructor.
    + by apply fve_svar0; constructor.
  - intro a; rewrite !elem_of_filtered_intersection.
    apply forall_proper; intro A.
    rewrite IHphi; [done |].
    split; intros x Hx.
    + by apply fve_evar0; constructor.
    + cbn; unfold fn_update; case_decide; [done |].
      by apply fve_svar0; constructor.
  - intro a; rewrite !elem_of_ext_iapp.
    setoid_rewrite (IHphi1 e1 e2); [setoid_rewrite (IHphi2 e1 e2) |]; [done |..];
      split; intros.
    + by apply fve_evar0, ef_app_right.
    + by apply fve_svar0, sf_app_right.
    + by apply fve_evar0, ef_app_left.
    + by apply fve_svar0, sf_app_left.
  - done.
Qed.

Lemma ClosedPattern_FV_equal (phi : Pattern) (e1 e2 : Valuation) :
  ClosedPattern phi -> FV_equal e1 e2 phi.
Proof. intros []; split; intros x Hx; contradict Hx; done. Qed.

Lemma pattern_valuation_closed_pattern e1 e2 phi :
  ClosedPattern phi -> pattern_valuation e1 phi ≡ pattern_valuation e2 phi.
Proof. by intro; apply pattern_valuation_fv, ClosedPattern_FV_equal. Qed.

Definition evaluates_to_singleton (e : Valuation) (phi : Pattern) : Prop :=
  exists a, pattern_valuation e phi ≡ {[a]}.

Class always_evaluates_to_singleton (phi : Pattern) : Prop :=
{
  aes : forall (e : Valuation), evaluates_to_singleton e phi
}.

#[export] Instance always_evaluates_to_singleton_evar x :
  always_evaluates_to_singleton (PEVar x).
Proof. by constructor; intros; eexists. Qed.

Definition singleton_value
  (phi : Pattern) `{!always_evaluates_to_singleton phi}
  (e : Valuation) : { a : idomain | pattern_valuation e phi ≡ {[a]} }.
Proof.
  destruct always_evaluates_to_singleton0.
  specialize (aes0 e).
  by apply constructive_indefinite_description in aes0.
Qed.

Lemma pattern_valuation_evar_sub0_not_free e x delta phi c :
  ~ EVarFree x phi ->
  pattern_valuation e (evar_sub0 x delta phi)
    ≡
  pattern_valuation (valuation_eupdate e x c) phi.
Proof.
  intro; erewrite evar_sub0_not_free by done.
  apply pattern_valuation_fv; split; [| done].
  intros y Hy; cbn; unfold fn_update.
  by case_decide; subst.
Qed.

Lemma pattern_valuation_evar_sub0 e x delta phi
  `{!always_evaluates_to_singleton delta} :
  EFreeFor x delta phi ->
  pattern_valuation e (evar_sub0 x delta phi)
    ≡
  pattern_valuation (valuation_eupdate e x (` (singleton_value delta e))) phi.
Proof.
  remember (proj1_sig _) as c.
  intros Hfree_for.
  destruct (classic (EVarFree x phi)) as [Hfree |];
    [| by apply pattern_valuation_evar_sub0_not_free].
  revert e c Heqc; induction phi; try (by inversion Hfree); intros ? c Hc.
  - by inversion Hfree; subst; cbn; unfold fn_update;
      rewrite !decide_True by done; destruct singleton_value.
  - rewrite pattern_valuation_impl_alt_classic by done.
    apply EFreeForImpl in Hfree_for as [Hfree_for1 Hfree_for2].
    destruct (classic (EVarFree x phi1)); [destruct (classic (EVarFree x phi2)) |].
    + rewrite <- IHphi1, <- IHphi2 by done.
      by apply pattern_valuation_impl_alt_classic.
    + rewrite <- IHphi1, <- pattern_valuation_evar_sub0_not_free
        with (phi := phi2) (delta := delta) by done.
      by apply pattern_valuation_impl_alt_classic.
    + inversion Hfree; [done | subst].
      rewrite <- IHphi2, <- pattern_valuation_evar_sub0_not_free
        with (phi := phi1) (delta := delta) by done.
      by apply pattern_valuation_impl_alt_classic.
  - apply EFreeForEx in Hfree_for as [Hfree_for1 Hx].
    inversion Hfree; subst y phi0.
    cbn; rewrite decide_False by done; cbn.
    intro a; rewrite !elem_of_indexed_union.
    setoid_rewrite IHphi; [| done..].
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
    setoid_rewrite IHphi; [| done..].
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
    destruct (classic (EVarFree x phi1)); [destruct (classic (EVarFree x phi2)) |].
    + by rewrite <- IHphi1, <- IHphi2.
    + by rewrite <- IHphi1, <- pattern_valuation_evar_sub0_not_free
        with (phi := phi2) (delta := delta).
    + inversion Hfree; [done | subst].
      by rewrite <- IHphi2, <- pattern_valuation_evar_sub0_not_free
        with (phi := phi1) (delta := delta).
Qed.

Lemma pattern_valuation_evar_sub0_evar e x y phi :
  EFreeFor x (PEVar y) phi ->
  pattern_valuation e (evar_sub0 x (PEVar y) phi)
    ≡
  pattern_valuation (valuation_eupdate e x (eval e y)) phi.
Proof.
  intro Hfree_for.
  unshelve rewrite pattern_valuation_evar_sub0 by done;
    [typeclasses eauto |].
  destruct (singleton_value (PEVar y) e); cbn in *.
  by apply singleton_equiv_inj in e0 as <-.
Qed.

End sec_pattern_valuation.
