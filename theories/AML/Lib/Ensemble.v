From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From Coq Require Import Classical.

Section sec_ensemble.

Definition Ensemble (idomain : Type) : Type := idomain -> Prop.

Definition top (idomain : Type) : Ensemble idomain := const true.

Context
  [idomain : Type].


#[export] Instance pow_set_elem_of : ElemOf idomain (Ensemble idomain) := fun x A => A x.
#[export] Instance pow_set_empty : Empty (Ensemble idomain) := const False.
#[export] Instance pow_set_singleton : Singleton idomain (Ensemble idomain) :=
  fun x => fun y => y = x.
#[export] Instance pow_set_union : Union (Ensemble idomain) :=
  fun A B => fun x => x ∈ A \/ x ∈ B.
#[export] Instance pow_set_intersection : Intersection (Ensemble idomain) :=
  fun A B => fun x => x ∈ A /\ x ∈ B.
#[export] Instance pow_set_difference : Difference (Ensemble idomain) :=
  fun A B => fun x => x ∈ A /\ x ∉ B.
#[export] Instance pow_set_semiset : SemiSet idomain (Ensemble idomain).
Proof. by split; [inversion 1 |..]. Qed.
#[export] Instance pow_set_set : Set_ idomain (Ensemble idomain).
Proof. by split; [typeclasses eauto |..]. Qed.

Definition complement (A : Ensemble idomain) : Ensemble idomain := fun a => a ∉ A.

Lemma elem_of_equiv_top X : X ≡ top idomain ↔ ∀ x, x ∈ X.
Proof. set_solver. Qed.

Lemma top_subseteq_equiv A : top idomain ⊆ A <-> A ≡ top idomain.
Proof. by split; intro Hsub; [split; [done |] | intro]; apply Hsub. Qed.

Definition filtered_union
    `(P : index -> Prop) (A : index -> (Ensemble idomain)) : (Ensemble idomain) :=
  fun a => exists i, P i /\ a ∈ A i.

Lemma elem_of_filtered_union
    a `(P : index -> Prop) (A : index -> (Ensemble idomain)) :
  a ∈ filtered_union P A <-> exists i, P i /\ a ∈ A i.
Proof. done. Qed.

Lemma member_of_filtered_union `(P : index -> Prop) (A : index -> (Ensemble idomain)) i :
  P i -> A i ⊆ filtered_union P A.
Proof. by intros Hi a HAi; apply elem_of_filtered_union; eexists. Qed.

Lemma empty_filtered_union `(P : index -> Prop) (A : index -> (Ensemble idomain)) :
  filtered_union P A ≡ ∅ <-> forall i, P i -> A i ≡ ∅.
Proof.
  split.
  - intros Hunion i; rewrite elem_of_equiv_empty; intros Hi a Ha.
    by apply (Hunion a), elem_of_filtered_union; eexists.
  - intro Hunion; rewrite elem_of_equiv_empty; intro a.
    rewrite elem_of_filtered_union; intros (? & ? & ?).
    by eapply Hunion.
Qed.

Definition indexed_union {index} : (index -> (Ensemble idomain)) -> (Ensemble idomain) :=
  filtered_union (const True).

Lemma elem_of_indexed_union a `(A : index -> (Ensemble idomain)) :
  a ∈ indexed_union A <-> exists i, a ∈ A i.
Proof.
  unfold indexed_union; rewrite elem_of_filtered_union.
  by split; intros [i Hi]; exists i; [apply Hi | split].
Qed.

Lemma member_of_indexed_union `(A : index -> (Ensemble idomain)) i :
  A i ⊆ indexed_union A.
Proof. by apply member_of_filtered_union. Qed.

Lemma empty_indexed_union `(A : index -> (Ensemble idomain)) :
  indexed_union A ≡ ∅ <-> forall i, A i ≡ ∅.
Proof.
  unfold indexed_union; rewrite empty_filtered_union.
  cbn; itauto.
Qed.

Definition filtered_intersection
    `(P : index -> Prop) (A : index -> (Ensemble idomain)) : (Ensemble idomain) :=
  fun a => forall i, P i -> a ∈ A i.

Lemma elem_of_filtered_intersection
    a `(P : index -> Prop) (A : index -> (Ensemble idomain)) :
  a ∈ filtered_intersection P A <-> forall i, P i -> a ∈ A i.
Proof. done. Qed.

Lemma member_of_filtered_intersection `(P : index -> Prop) (A : index -> (Ensemble idomain)) i :
  P i -> filtered_intersection P A ⊆ A i.
Proof. by intros Hi a; rewrite elem_of_filtered_intersection; intros HA; apply HA. Qed.

Lemma filtered_intersection_empty_top
    `(P : index -> Prop) (A : index -> (Ensemble idomain)) :
  (forall i, ~ P i) -> filtered_intersection P A ≡ top idomain.
Proof.
  intros HnP; apply elem_of_equiv_top; intro a.
  apply elem_of_filtered_intersection; intros i HPi.
  by exfalso; eapply HnP.
Qed.

Definition indexed_intersection {index} : (index -> (Ensemble idomain)) -> (Ensemble idomain) :=
  filtered_intersection (const True).

Lemma elem_of_indexed_intersection a `(A : index -> (Ensemble idomain)) :
  a ∈ indexed_intersection A <-> forall i, a ∈ A i.
Proof.
  unfold indexed_intersection; rewrite elem_of_filtered_intersection.
  by split; intros Hall **; apply Hall.
Qed.

Lemma member_of_indexed_intersection `(A : index -> (Ensemble idomain)) i :
  indexed_intersection A ⊆ A i.
Proof. by apply member_of_filtered_intersection. Qed.

Definition intersection_list : list (Ensemble idomain) → Ensemble idomain :=
  fold_right (∩) (top idomain).
Notation "⋂ l" := (intersection_list l) (at level 20, format "⋂ l") : stdpp_scope.

Lemma elem_of_intersection_list Xs x : x ∈ ⋂ Xs ↔ forall X, X ∈ Xs -> x ∈ X.
Proof.
  split.
  - induction Xs; simpl; intros HXs; [inversion 1|].
    setoid_rewrite elem_of_cons. rewrite elem_of_intersection in HXs. naive_solver.
  - induction Xs; intro HXs; [done |].
    simpl; apply elem_of_intersection; split; [apply HXs | apply IHXs]; [left |].
    by intros; apply HXs; right.
Qed.

Definition sym_diff (A B : (Ensemble idomain)) : (Ensemble idomain) := (A ∖ B) ∪ (B ∖ A).

#[export] Instance complement_subseteq_proper : Proper ((⊆) ==> flip (⊆)) complement.
Proof.
  intros B C Hbc a; unfold complement, elem_of, pow_set_elem_of.
  by intro Hb; contradict Hb; apply Hbc.
Qed.

#[export] Instance complement_equiv_proper : Proper ((≡) ==> (≡)) complement.
Proof.
  intros B C; rewrite !set_equiv_subseteq.
  intros [Hbc Hcb]; split.
  - by change (flip (⊆) (complement C) (complement B)); rewrite Hcb.
  - by change (flip (⊆) (complement B) (complement C)); rewrite Hbc.
Qed.

Lemma elem_of_complement a A : a ∈ complement A <-> a ∉ A.
Proof. done. Qed.

Lemma complement_top A : complement A ≡ top idomain <-> A ≡ ∅.
Proof.
  split; [| intros ->].
  - intros Hcompl a; split; [| done]; intro Ha.
    destruct (Hcompl a) as [_ Hcompl'].
    by feed specialize Hcompl'.
  - by rewrite elem_of_equiv_top; intro; apply elem_of_complement, not_elem_of_empty.
Qed.

Lemma complement_twice_classic A : complement (complement A) ≡ A.
Proof.
  intro a; rewrite !elem_of_complement.
  split; [| by intros ? ?].
  by intro; apply NNPP.
Qed.

Lemma complement_empty_classic A : complement A ≡ ∅ <-> A ≡ top idomain.
Proof.
  by rewrite <- complement_top, complement_twice_classic.
Qed.

Lemma complement_union_classic A B :
  complement (A ∪ B) ≡ complement A ∩ complement B.
Proof.
  intro a; rewrite elem_of_intersection, !elem_of_complement, elem_of_union.
  by split; [apply not_or_and | intros [] []].
Qed.

Lemma complement_intersection_classic A B :
  complement (A ∩ B) ≡ complement A ∪ complement B.
Proof.
  intro a; rewrite elem_of_union, !elem_of_complement, elem_of_intersection.
  by split; [apply not_and_or | intros [] []].
Qed.

Lemma complement_filtered_union `(P : index -> Prop) (A : index -> (Ensemble idomain)) :
  complement (filtered_union P A) ≡ filtered_intersection P (complement ∘ A).
Proof.
  intro x; rewrite elem_of_filtered_intersection; setoid_rewrite elem_of_complement;
    rewrite elem_of_filtered_union.
  split; [| by intros Hix (i & Hi & Hx); eapply Hix].
  by intros Hnix i Hi; contradict Hnix; eexists.
Qed.

Lemma complement_indexed_union `(f : index -> (Ensemble idomain)) :
  complement (indexed_union f) ≡ indexed_intersection (complement ∘ f).
Proof. by unfold indexed_union; rewrite complement_filtered_union. Qed.

Lemma complement_filtered_intersection_classic `(P : index -> Prop) `(A : index -> (Ensemble idomain)) :
  complement (filtered_intersection P A) ≡ filtered_union P (complement ∘ A).
Proof.
  intro x; rewrite elem_of_filtered_union; setoid_rewrite elem_of_complement;
    rewrite elem_of_filtered_intersection.
  split; [| by intros (i & Hi & Hx); contradict Hx; apply Hx].
  intros Hnot; apply not_all_ex_not in Hnot as [i Hnot].
  by eexists; apply imply_to_and in Hnot.
Qed.

Lemma complement_indexed_intersection_classic `(f : index -> (Ensemble idomain)) :
  complement (indexed_intersection f) ≡ indexed_union (complement ∘ f).
Proof.
  by unfold indexed_intersection; rewrite complement_filtered_intersection_classic.
Qed.

#[export]  Instance intersection_empty_l : LeftId (≡@{(Ensemble idomain)}) (top idomain) (∩).
Proof. intros X. set_solver. Qed.
#[export] Instance intersection_empty_r : RightId (≡@{(Ensemble idomain)}) (top idomain) (∩).
Proof. intros X. set_solver. Qed.

Lemma top_intersection A B : A ∩ B ≡ top idomain <-> A ≡ top idomain /\ B ≡ top idomain.
Proof. set_solver. Qed.

Lemma top_filtered_intersection `(P : index -> Prop) (f : index -> (Ensemble idomain)) :
  filtered_intersection P f ≡ top idomain
    <->
  forall B, P B -> f B ≡ top idomain.
Proof.
  setoid_rewrite elem_of_equiv_top; setoid_rewrite elem_of_filtered_intersection.
  itauto.
Qed.

Lemma top_indexed_intersection (f : Ensemble idomain -> Ensemble idomain) :
  indexed_intersection f ≡ top idomain
    <->
  forall B, f B ≡ top idomain.
Proof.
  unfold indexed_intersection. rewrite top_filtered_intersection; cbn; itauto.
Qed.

Lemma intersection_list_cons X Xs : ⋂ (X :: Xs) = X ∩ ⋂ Xs.
Proof. done. Qed.

Lemma top_intersection_list Xs :
  ⋂ Xs ≡ top idomain <-> Forall (fun X => X ≡ top idomain) Xs.
Proof.
  induction Xs; [by cbn; split; [constructor |] |].
  by rewrite intersection_list_cons, top_intersection, Forall_cons, IHXs.
Qed.

Lemma difference_alt A B : A ∖ B ≡ A ∩ complement B.
Proof. set_solver. Qed.

Lemma subseteq_empty_difference_classic (X Y : (Ensemble idomain)) : X ⊆ Y <-> X ∖ Y ≡ ∅.
Proof.
  split; [apply subseteq_empty_difference |].
  intros Hxy a Ha; destruct (Hxy a) as [Hxy' _].
  rewrite elem_of_difference in Hxy'.
  destruct (classic (a ∈ Y)); [done | exfalso].
  by apply Hxy'.
Qed.

#[export] Instance sym_diff_proper : Proper ((≡) ==> (≡) ==> (≡)) sym_diff.
Proof. by intros A B Hab C D Hcd; unfold sym_diff; rewrite Hab, Hcd. Qed.

Lemma sym_diff_empty_classic A B : sym_diff A B ≡ ∅ <-> A ≡ B.
Proof.
  unfold sym_diff; split; [| intros ->].
  - intros Hab x; specialize (Hab x).
    rewrite elem_of_union, !elem_of_difference in Hab; split.
    + intros Ha.
      destruct (classic (x ∈ B)); [done |].
      by exfalso; apply Hab; left; split.
    + intros Hb.
      destruct (classic (x ∈ A)); [done |].
      by exfalso; apply Hab; right; split.
  - apply elem_of_equiv_empty; intro x.
    rewrite elem_of_union, !elem_of_difference.
    by intros [[] | []].
Qed.

Inductive CrispSet (A : Ensemble idomain) : Prop :=
| cs_empty : A ≡ ∅ -> CrispSet A
| cs_top : A ≡ top idomain -> CrispSet A.

End sec_ensemble.

Notation "⋂ l" := (intersection_list l) (at level 20, format "⋂ l") : stdpp_scope.

Section SecKnasterTarski.

Context
  {idomain : Type}
  (F : Ensemble idomain -> Ensemble idomain)
  `{!Proper ((⊆) ==> (⊆)) F}.

Definition lfp : Ensemble idomain :=
  filtered_intersection (fun B => F B ⊆ B) id.

Lemma elem_of_lfp x : x ∈ lfp <-> forall A, F A ⊆ A -> x ∈ A.
Proof. by apply elem_of_filtered_intersection. Qed.

Lemma knaster_tarsky_least_pre_fixpoint A :
  F A ⊆ A -> lfp ⊆ A.
Proof.
  intros HA a; rewrite elem_of_lfp.
  by intro Hall; apply Hall in HA.
Qed.

Lemma knaster_tarsky_lfp_least A :
  F A ≡ A -> lfp ⊆ A.
Proof.
  intro HA; apply set_equiv_subseteq in HA as [HA _].
  by apply knaster_tarsky_least_pre_fixpoint.
Qed.

Lemma knaster_tarsky_lfp_fix :
  F lfp ≡ lfp.
Proof.
  apply set_equiv_subseteq.
  cut (F lfp ⊆ lfp); [intros Hincl; split; [done |] |].
  - intro a; rewrite elem_of_lfp.
    by intro Hall; apply Proper0, Hall in Hincl.  
  - intro a; rewrite elem_of_lfp.
    intros Ha B HB.
    apply HB.
    assert (Hincl : lfp ⊆ B)
      by (apply knaster_tarsky_least_pre_fixpoint; done).
    by apply Proper0 in Hincl; apply Hincl.
Qed.

Definition gfp : Ensemble idomain :=
  filtered_union (fun B => B ⊆ F B) id.

Lemma elem_of_gfp x : x ∈ gfp <-> exists A, A ⊆ F A /\ x ∈ A.
Proof. by apply elem_of_filtered_union. Qed.

Lemma knaster_tarsky_greatest_post_fixpoint A :
  A ⊆ F A -> A ⊆ gfp.
Proof.
  by intros HA a Ha; rewrite elem_of_gfp; eexists.
Qed.

Lemma knaster_tarsky_gfp_greatest A :
  F A ≡ A -> A ⊆ gfp.
Proof.
  intro HA; apply set_equiv_subseteq in HA as [_ HA].
  by apply knaster_tarsky_greatest_post_fixpoint.
Qed.

Lemma knaster_tarsky_gfp_fix :
  F gfp ≡ gfp.
Proof.
  apply set_equiv_subseteq.
  cut (gfp ⊆ F gfp); [intros Hincl; split; [| done] |].
  - intros a Ha; rewrite elem_of_gfp.
    by apply Proper0 in Hincl; eexists.
  - intro a; rewrite elem_of_gfp.
    intros (A & HA & Ha).
    assert (Hincl : A ⊆ gfp)
      by (apply knaster_tarsky_greatest_post_fixpoint; done).
    by apply Proper0 in Hincl; apply Hincl, HA.
Qed.

End SecKnasterTarski.
