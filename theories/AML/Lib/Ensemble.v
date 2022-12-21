From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From Coq Require Import Classical.
From AML Require Import Functions.

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

Lemma filtered_intersection_subseteq_filtered_union
  `(P : index -> Prop) (A : index -> (Ensemble idomain)) :
   (exists i, P i) -> filtered_intersection P A ⊆ filtered_union P A.
Proof.
  intros [] a; rewrite elem_of_filtered_intersection, elem_of_filtered_union.
  by intros Hall; eexists; split; [| apply Hall].
Qed.

Lemma indexed_intersection_subseteq_indexed_union
  `{Inhabited index} (A : index -> (Ensemble idomain)) :
  indexed_intersection A ⊆ indexed_union A.
Proof.
  apply filtered_intersection_subseteq_filtered_union.
  by exists inhabitant.
Qed.

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

#[export] Instance complement_subseteq_proper : Proper ((⊆) --> (⊆)) complement.
Proof.
  intros B C Hbc a; unfold complement, elem_of, pow_set_elem_of.
  by intro Hb; contradict Hb; apply Hbc.
Qed.

Lemma complement_subseteq_iff_classic B C : B ⊆ C <-> complement C ⊆ complement B.
Proof.
  split; [apply complement_subseteq_proper |].
  intros Hbc b Hb.
  destruct (classic (b ∈ C)); [done |].
  by contradict Hb; apply Hbc.
Qed.

#[export] Instance complement_equiv_proper : Proper ((≡) ==> (≡)) complement.
Proof.
  intros B C; rewrite !set_equiv_subseteq.
  intros [Hbc Hcb]; split.
  - by rewrite <- Hcb.
  - by rewrite <- Hbc.
Qed.

Lemma complement_equiv_proper_iff_classic B C : B ≡ C <-> complement B ≡ complement C.
Proof.
  by rewrite !set_equiv_subseteq, <- !complement_subseteq_iff_classic; set_solver.
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

Definition ascending_chain (C : nat -> Ensemble idomain) : Prop :=
  forall n, C n ⊆ C (S n).

Lemma ascending_chain_skipping (C : nat -> Ensemble idomain) :
  ascending_chain C -> forall m n, m <= n -> C m ⊆ C n.
Proof.
  intros HC m n; revert m; induction n.
  - by intros m Hm; replace m with 0 by lia.
  - intros m Hm; destruct (decide (m = S n)); [by subst |].
    etransitivity; [| apply HC].
    apply IHn; lia.
Qed.

Lemma proper_compose_ascending_chain
  (F : Ensemble idomain -> Ensemble idomain) `{!Proper ((⊆) ==> (⊆)) F}
  (C : nat -> Ensemble idomain) :
  ascending_chain C -> ascending_chain (F ∘ C).
Proof. by intros HC n; apply Proper0, HC. Qed.

Definition descending_chain (C : nat -> Ensemble idomain) : Prop :=
  forall n, C (S n) ⊆ C n.

Lemma descending_chain_skipping (C : nat -> Ensemble idomain) :
  descending_chain C -> forall m n, m <= n -> C n ⊆ C m.
Proof.
  intros HC m n; revert m; induction n.
  - by intros m Hm; replace m with 0 by lia.
  - intros m Hm; destruct (decide (m = S n)); [by subst |].
    etransitivity; [apply HC |].
    apply IHn; lia.
Qed.

Lemma proper_compose_descending_chain
  (F : Ensemble idomain -> Ensemble idomain) `{!Proper ((⊆) ==> (⊆)) F}
  (C : nat -> Ensemble idomain) :
  descending_chain C -> descending_chain (F ∘ C).
Proof. by intros HC n; apply Proper0, HC. Qed.

Lemma ascending_chain_descending (C : nat -> Ensemble idomain) :
  ascending_chain C -> descending_chain (complement ∘ C).
Proof.
  intros Hasc n; cbn; intro a; cbn; rewrite !elem_of_complement.
  by unfold ascending_chain in Hasc; set_solver.
Qed.

Lemma descending_chain_ascending (C : nat -> Ensemble idomain) :
  descending_chain C -> ascending_chain (complement ∘ C).
Proof.
  intros Hasc n; cbn; intro a; cbn; rewrite !elem_of_complement.
  by unfold descending_chain in Hasc; set_solver.
Qed.

End sec_ensemble.

Section sec_ensemble_maps.

Definition image `(F : A -> Ensemble B) (X : Ensemble A) : Ensemble B :=
  filtered_union (fun x : A => x ∈ X) F.

Lemma image_singleton `(F : A -> Ensemble B) (a : A) :
  F a ≡ image F {[ a ]}.
Proof.
  intro x; unfold image.
  rewrite elem_of_filtered_union.
  setoid_rewrite elem_of_singleton.
  by set_solver.
Qed.

Lemma elem_of_image `(F : A -> Ensemble B) (X : Ensemble A) (b : B) :
  b ∈ image F X <-> exists a, a ∈ X /\ b ∈ F a.
Proof. by apply elem_of_filtered_union. Qed.

Definition fiber `(F : A -> Ensemble B) (y : B) : Ensemble A := 
  filtered_union (fun x : A => y ∈ F x) singleton.

Lemma elem_of_fiber `(F : A -> Ensemble B) (b : B) (a : A) :
  a ∈ fiber F b <-> b ∈ F a.
Proof.
  unfold fiber; rewrite elem_of_filtered_union.
  by set_solver.
Qed.

Definition preimage {A B : Type} : (A -> Ensemble B) -> Ensemble B -> Ensemble A := 
  image ∘ fiber.

Lemma elem_of_preimage `(F : A -> Ensemble B) (Y : Ensemble B) (a : A) :
  a ∈ preimage F Y <-> exists y, y ∈ Y /\ y ∈ F a.
Proof.
  unfold preimage; cbn.
  rewrite elem_of_image.
  by setoid_rewrite elem_of_fiber.
Qed.

End sec_ensemble_maps.

Notation "⋂ l" := (intersection_list l) (at level 20, format "⋂ l") : stdpp_scope.

Section SecKnasterTarski.

Context
  {idomain : Type}
  (F : Ensemble idomain -> Ensemble idomain)
  `{!Proper ((⊆) ==> (⊆)) F}.

Definition pre_fixpoint (B : Ensemble idomain) : Prop := F B ⊆ B.
Definition post_fixpoint (B : Ensemble idomain) : Prop := B ⊆ F B.
Definition fixpoint (B : Ensemble idomain) : Prop := F B ≡ B.

Definition lfp : Ensemble idomain := filtered_intersection pre_fixpoint id.

Lemma elem_of_lfp x : x ∈ lfp <-> forall A, pre_fixpoint A -> x ∈ A.
Proof. by apply elem_of_filtered_intersection. Qed.

Lemma knaster_tarsky_least_pre_fixpoint A :
  pre_fixpoint A -> lfp ⊆ A.
Proof.
  intros HA a; rewrite elem_of_lfp.
  by intro Hall; apply Hall in HA.
Qed.

Lemma knaster_tarsky_lfp_least A :
  fixpoint A -> lfp ⊆ A.
Proof.
  intro HA; apply set_equiv_subseteq in HA as [HA _].
  by apply knaster_tarsky_least_pre_fixpoint.
Qed.

Lemma knaster_tarsky_lfp_fix : fixpoint lfp.
Proof.
  apply set_equiv_subseteq.
  cut (pre_fixpoint lfp); [intros Hincl; split; [done |] |].
  - intro a; rewrite elem_of_lfp.
    by intro Hall; apply Proper0, Hall in Hincl.
  - intro a; rewrite elem_of_lfp.
    intros Ha B HB.
    apply HB.
    assert (Hincl : lfp ⊆ B)
      by (apply knaster_tarsky_least_pre_fixpoint; done).
    by apply Proper0 in Hincl; apply Hincl.
Qed.

Lemma knaster_tarsky_lfp_fix_sub A : A ⊆ lfp -> F A ⊆ lfp.
Proof.
  intro Hincl.
  transitivity (F lfp); [by apply Proper0 |].
  by apply set_equiv_subseteq; symmetry; apply knaster_tarsky_lfp_fix.
Qed.

Definition gfp : Ensemble idomain := filtered_union post_fixpoint id.

Lemma elem_of_gfp x : x ∈ gfp <-> exists A, post_fixpoint A /\ x ∈ A.
Proof. by apply elem_of_filtered_union. Qed.

Lemma knaster_tarsky_greatest_post_fixpoint A :
  post_fixpoint A -> A ⊆ gfp.
Proof.
  by intros HA a Ha; rewrite elem_of_gfp; eexists.
Qed.

Lemma knaster_tarsky_gfp_greatest A :
  fixpoint A -> A ⊆ gfp.
Proof.
  intro HA; apply set_equiv_subseteq in HA as [_ HA].
  by apply knaster_tarsky_greatest_post_fixpoint.
Qed.

Lemma knaster_tarsky_gfp_fix : fixpoint gfp.
Proof.
  apply set_equiv_subseteq.
  cut (post_fixpoint gfp); [intros Hincl; split; [| done] |].
  - intros a Ha; rewrite elem_of_gfp.
    by apply Proper0 in Hincl; eexists.
  - intro a; rewrite elem_of_gfp.
    intros (A & HA & Ha).
    assert (Hincl : A ⊆ gfp)
      by (apply knaster_tarsky_greatest_post_fixpoint; done).
    by apply Proper0 in Hincl; apply Hincl, HA.
Qed.

Lemma knaster_tarsky_gfp_fix_sub A : gfp ⊆ A -> gfp ⊆ F A.
Proof.
  intro Hincl.
  transitivity (F gfp); [| by apply Proper0].
  by apply set_equiv_subseteq; apply knaster_tarsky_gfp_fix.
Qed.

End SecKnasterTarski.

Section sec_fix_points_props.

Context
  {idomain : Type}
  (F G : Ensemble idomain -> Ensemble idomain)
  (Hext : forall A, F A ≡ G A).

Lemma pre_fixpoint_equiv B :
  pre_fixpoint F B <-> pre_fixpoint G B.
Proof. by unfold pre_fixpoint; rewrite Hext. Qed.

Lemma post_fixpoint_equiv B :
  post_fixpoint F B <-> post_fixpoint G B.
Proof. by unfold post_fixpoint; rewrite Hext. Qed.

Lemma fixpoint_equiv B :
  fixpoint F B <-> fixpoint G B.
Proof. by unfold fixpoint; rewrite Hext. Qed.

End sec_fix_points_props.

Class Continuous {idomain : Type} (F : Ensemble idomain -> Ensemble idomain) : Prop :=
{
  continuous : forall (C : nat -> Ensemble idomain),
    F (indexed_union C) ≡ indexed_union (F ∘ C)
}.

Class OmegaContinuous {idomain : Type} (F : Ensemble idomain -> Ensemble idomain) : Prop :=
{
  omega_continuous : forall (C : nat -> Ensemble idomain),
    ascending_chain C -> F (indexed_union C) ≡ indexed_union (F ∘ C)
}.

#[export] Instance ContinuousOmega `{Continuous idomain F} : OmegaContinuous F.
Proof. by constructor; intros; apply continuous. Qed.

Class CoContinuous {idomain : Type} (F : Ensemble idomain -> Ensemble idomain) : Prop :=
{
  co_continuous : forall (C : nat -> Ensemble idomain),
    F (indexed_intersection C) ≡ indexed_intersection (F ∘ C)
}.

Class CoOmegaContinuous {idomain : Type} (F : Ensemble idomain -> Ensemble idomain) : Prop :=
{
  co_omega_continuous : forall (C : nat -> Ensemble idomain),
    descending_chain C -> F (indexed_intersection C) ≡ indexed_intersection (F ∘ C)
}.


#[export] Instance CoContinuousOmega `{CoContinuous idomain F} : CoOmegaContinuous F.
Proof. by constructor; intros; apply co_continuous. Qed.

Section SecKleeneFixPoint.

Context
  {idomain : Type}
  (F : Ensemble idomain -> Ensemble idomain)
  `{!Proper ((⊆) ==> (⊆)) F}.

#[export] Instance pow_compose_monotone n : Proper ((⊆) ==> (⊆)) (pow_compose F n).
Proof.
  induction n; cbn; [by typeclasses eauto |].
  by intros ? ? ?; apply Proper0, IHn.
Qed.

Lemma pre_fixpoint_pow_compose A n : pre_fixpoint F A -> pow_compose F n A ⊆ A.
Proof.
  intros Hpre; induction n; [done |].
  by etransitivity; [apply Proper0 | apply Hpre].
Qed.

Definition klfp : Ensemble idomain := indexed_union (fun n => pow_compose F n ∅).

Lemma elem_of_klfp x : x ∈ klfp <-> exists n, x ∈ pow_compose F n ∅.
Proof. by apply elem_of_indexed_union. Qed.

Lemma member_of_klfp n : pow_compose F n ∅ ⊆ klfp.
Proof. by apply (member_of_indexed_union (fun n => pow_compose F n ∅)). Qed.

Lemma klfp_unfold :
  klfp ≡ indexed_union (F ∘ (λ n : nat, pow_compose F n ∅)).
Proof.
  intro a; rewrite elem_of_indexed_union, elem_of_klfp; cbn; split.
  - by intros [[] Ha]; [by contradict Ha; apply not_elem_of_empty | exists n].
  - by intros [n Ha]; exists (S n).
Qed.

Lemma kleene_ascending_chain : ascending_chain (fun n => pow_compose F n ∅).
Proof. by intro n; induction n; [set_solver | apply Proper0]. Qed.

Lemma klfp_post_fixpoint : post_fixpoint F klfp.
Proof.
  unfold post_fixpoint.
  etransitivity; [by rewrite klfp_unfold |].
  intro a; rewrite elem_of_indexed_union.
  cbn; intros [n Ha].
  cut (F (pow_compose F n ∅) ⊆ F klfp); [by set_solver |].
  by apply Proper0, member_of_klfp.
Qed.

Lemma pow_compose_F_n_empty_subseteq_pre_fixpoint
  A (HA : pre_fixpoint F A) n :
  pow_compose F n ∅ ⊆ A.
Proof.
  induction n; cbn; [by set_solver |].
  by transitivity (F A); [apply Proper0 |].
Qed.

Lemma kleene_least_pre_fixpoint A : pre_fixpoint F A -> klfp ⊆ A.
Proof.
  intros HA a; rewrite elem_of_klfp.
  intros [n Ha].
  by eapply pow_compose_F_n_empty_subseteq_pre_fixpoint.
Qed.

Lemma klfp_subseteq_lfp : klfp ⊆ lfp F.
Proof.
  intros x Hx; apply elem_of_lfp.
  by intros A HA; apply kleene_least_pre_fixpoint.
Qed.

Lemma kleene_lfp_least A :
  fixpoint F A -> klfp ⊆ A.
Proof.
  intro HA; etransitivity.
  - by apply klfp_subseteq_lfp.
  - by apply knaster_tarsky_lfp_least.
Qed.

Lemma klfp_fixpoint_elim :
  pre_fixpoint F klfp -> fixpoint F klfp.
Proof.
  by intro; apply set_equiv_subseteq; split; [| apply klfp_post_fixpoint].
Qed.

Lemma Omega_continuous_klfp_fixpoint `{!OmegaContinuous F} : fixpoint F klfp.
Proof.
  unfold fixpoint.
  etransitivity; [| by rewrite klfp_unfold].
  by apply omega_continuous, kleene_ascending_chain.
Qed.

Lemma kleene_knaster_tarsky_lfp_equiv :
  fixpoint F klfp -> lfp F ≡ klfp.
Proof.
  intro Hfix; apply set_equiv_subseteq; split.
  - by apply knaster_tarsky_lfp_least, Hfix.
  - by apply klfp_subseteq_lfp.
Qed.

Definition kgfp : Ensemble idomain :=
  indexed_intersection (fun n => pow_compose F n (top idomain)).

Lemma elem_of_kgfp x : x ∈ kgfp <-> forall n, x ∈ pow_compose F n (top idomain).
Proof. by apply elem_of_indexed_intersection. Qed.

Lemma member_of_kgfp n : kgfp ⊆ pow_compose F n (top idomain).
Proof. apply (member_of_indexed_intersection (fun n => pow_compose F n (top idomain))). Qed.

Lemma kleene_descending_chain : descending_chain (fun n => pow_compose F n (top idomain)).
Proof. by intro n; induction n; [set_solver | apply Proper0]. Qed.

Lemma kgfp_unfold :
  kgfp ≡ indexed_intersection (F ∘ (λ n : nat, pow_compose F n (top idomain))).
Proof.
  intro a; rewrite elem_of_indexed_intersection, elem_of_kgfp; cbn; split.
  - by intros Hall n; apply (Hall (S n)).
  - by intros Hall []; [| apply Hall].
Qed.

Lemma kgfp_pre_fixpoint : pre_fixpoint F kgfp.
Proof.
  unfold pre_fixpoint.
  etransitivity; [| by rewrite kgfp_unfold].
  intro a; rewrite elem_of_indexed_intersection.
  cbn; intros Ha n.
  cut (F kgfp ⊆ F (pow_compose F n (top idomain))); [by set_solver |].
  by apply Proper0, member_of_kgfp.
Qed.

Lemma kgfp_fixpoint_elim :
  post_fixpoint F kgfp -> fixpoint F kgfp.
Proof.
  by intro; apply set_equiv_subseteq; split; [apply kgfp_pre_fixpoint |].
Qed.

Lemma co_Omega_continuous_kgfp_fixpoint `{!CoOmegaContinuous F} :
  fixpoint F kgfp.
Proof.
  unfold fixpoint.
  etransitivity; [| by rewrite kgfp_unfold].
  by apply co_omega_continuous, kleene_descending_chain.
Qed.

Lemma kleene_greatest_post_fixpoint A : post_fixpoint F A -> A ⊆ kgfp.
Proof.
  intros HA.
  cut (forall n, A ⊆ pow_compose F n (top idomain)).
  - by intros Hall a Ha; apply elem_of_kgfp; intro n; apply Hall.
  - induction n; [by set_solver | cbn].
    transitivity (F A); [done |].
    by apply Proper0.
Qed.

Lemma kleene_gfp_greatest A :
  fixpoint F A -> A ⊆ kgfp.
Proof.
  intro HA; apply set_equiv_subseteq in HA as [_ HA].
  by apply kleene_greatest_post_fixpoint.
Qed.

Lemma kleene_knaster_tarsky_gfp_equiv :
  fixpoint F kgfp -> gfp F ≡ kgfp.
Proof.
  intro Hfix; apply set_equiv_subseteq; split.
  - by apply kleene_gfp_greatest, knaster_tarsky_gfp_fix.
  - by apply knaster_tarsky_gfp_greatest, Hfix.
Qed.

End SecKleeneFixPoint.
