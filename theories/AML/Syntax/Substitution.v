From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From AML Require Import Signature Pattern Variables.

Section sec_substitution.

Context
  `{signature}.

Fixpoint evar_sub0 (x : EVar) (delta : Pattern) (p : Pattern) : Pattern :=
  match p with
  | PEVar y => if (decide (x = y)) then delta else p
  | PSVar _ => p
  | POp _ => p
  | PImpl ϕ ψ => PImpl (evar_sub0 x delta ϕ) (evar_sub0 x delta ψ)
  | PApp ϕ ψ => PApp (evar_sub0 x delta ϕ) (evar_sub0 x delta ψ)
  | PEx y ϕ =>  if (decide (x = y)) then p else PEx y (evar_sub0 x delta ϕ)
  | μₚ X ϕ => μₚ X (evar_sub0 x delta ϕ)
  end.

Lemma evar_sub0_evar_BEV x y ϕ :
  BEV (evar_sub0 x (PEVar y) ϕ) ≡ BEV ϕ.
Proof.
  induction ϕ; cbn; [| done |..| done].
  - by case_decide.
  - by set_solver.
  - by case_decide; set_solver.
  - done.
  - by set_solver.
Qed.

Lemma evar_sub0_evar_FSV x y ϕ :
  FSV (evar_sub0 x (PEVar y) ϕ) ≡ FSV ϕ.
Proof.
  induction ϕ; cbn.
  - by case_decide.
  - done.
  - set_solver.
  - case_decide; set_solver.
  - set_solver.
  - set_solver.
  - done.
Qed.

Lemma evar_sub0_evar_BSV x y ϕ :
  BSV (evar_sub0 x (PEVar y) ϕ) ≡ BSV ϕ.
Proof.
  induction ϕ; cbn.
  - by case_decide.
  - done.
  - set_solver.
  - case_decide; set_solver.
  - set_solver.
  - set_solver.
  - done.
Qed.

Lemma evar_sub0_evar_SV x y ϕ :
  SV (evar_sub0 x (PEVar y) ϕ) ≡ SV ϕ.
Proof.
  unfold SV; rewrite evar_sub0_evar_FSV, evar_sub0_evar_BSV; done.
Qed.

Lemma evar_sub0_not_occurs x to_replace replacement ϕ :
  ~ EOccurs x ϕ ->
  ~ EOccurs x replacement ->
  ~ EOccurs x (evar_sub0 to_replace replacement ϕ).
Proof.
  induction ϕ; cbn; try done.
  - by case_decide.
  - rewrite !EOccurs_impl; intros Hnϕ Hnrepl [|].
    + apply IHϕ1; [contradict Hnϕ; left |..]; done.
    + apply IHϕ2; [contradict Hnϕ; right |..]; done.
  - case_decide; rewrite !EOccurs_ex; intros Hnϕ Hnrepl [|].
    + contradict Hnϕ; left; done.
    + contradict Hnϕ; right; done.
    + contradict Hnϕ; left; done.
    + apply IHϕ; [contradict Hnϕ; right |..]; done.
  - by rewrite !EOccurs_mu.
  - rewrite !EOccurs_app; intros Hnϕ Hnrepl [|].
    + apply IHϕ1; [contradict Hnϕ; left |..]; done.
    + apply IHϕ2; [contradict Hnϕ; right |..]; done.
Qed.

Lemma evar_sub0_id x ϕ : evar_sub0 x (PEVar x) ϕ = ϕ.
Proof.
  induction ϕ; cbn. 2,7: done.
  - by case_decide; subst.
  - by rewrite IHϕ1, IHϕ2.
  - by rewrite IHϕ; case_decide.
  - by rewrite IHϕ.
  - by rewrite IHϕ1, IHϕ2.
Qed.

Fixpoint evar_rename (x y : EVar) (p : Pattern) : Pattern :=
  match p with
  | PEVar _ => p
  | PSVar _ => p
  | POp _ => p
  | PImpl ϕ ψ => PImpl (evar_rename x y ϕ) (evar_rename x y ψ)
  | PApp ϕ ψ => PApp (evar_rename x y ϕ) (evar_rename x y ψ)
  | PEx z ϕ =>
    if (decide (x = z))
      then (PEx y (evar_sub0 x (PEVar y) (evar_rename x y ϕ)))
      else PEx z (evar_rename x y ϕ)
  | μₚ X ϕ => μₚ X (evar_rename x y ϕ)
  end.

Lemma evar_rename_id x ϕ : evar_rename x x ϕ = ϕ.
Proof.
  induction ϕ; cbn. 1-2,7: done.
  - by rewrite IHϕ1, IHϕ2.
  - by rewrite IHϕ, evar_sub0_id; case_decide; subst.
  - by rewrite IHϕ.
  - by rewrite IHϕ1, IHϕ2.
Qed.

Lemma evar_rename_FSV x y ϕ :
  FSV (evar_rename x y ϕ) ≡ FSV ϕ.
Proof.
  induction ϕ; cbn; [done | done |..| done].
  - set_solver.
  - case_decide; cbn; [| done].
    by rewrite evar_sub0_evar_FSV.
  - set_solver.
  - set_solver.
Qed.

Lemma evar_rename_BSV x y ϕ :
  BSV (evar_rename x y ϕ) ≡ BSV ϕ.
Proof.
  induction ϕ; cbn; [done | done |..| done].
  - set_solver.
  - case_decide; cbn; [| done].
    by rewrite evar_sub0_evar_BSV.
  - set_solver.
  - set_solver.
Qed.

Lemma evar_rename_SV x y ϕ :
  SV (evar_rename x y ϕ) ≡ SV ϕ.
Proof.
  unfold SV; rewrite evar_rename_FSV, evar_rename_BSV; done.
Qed.

Definition evar_rename_iter (xs ys : list EVar) (p : Pattern) : Pattern :=
  foldr (fun (xy : EVar * EVar) (p : Pattern) => evar_rename xy.1 xy.2 p)
    p (zip xs ys).

Lemma evar_rename_iter_FSV (xs ys : list EVar) (ϕ : Pattern) :
  FSV (evar_rename_iter xs ys ϕ) ≡ FSV ϕ.
Proof.
  revert ys ϕ.
  induction xs; [done |].
  intros [|b ys] ϕ; [done |]; cbn.
  rewrite evar_rename_FSV.
  by apply IHxs.
Qed.

Lemma evar_rename_iter_BSV (xs ys : list EVar) (ϕ : Pattern) :
  BSV (evar_rename_iter xs ys ϕ) ≡ BSV ϕ.
Proof.
  revert ys ϕ.
  induction xs; [done |].
  intros [|b ys] ϕ; [done |]; cbn.
  rewrite evar_rename_BSV.
  by apply IHxs.
Qed.

Lemma evar_rename_iter_SV (xs ys : list EVar) (ϕ : Pattern) :
  SV (evar_rename_iter xs ys ϕ) ≡ SV ϕ.
Proof.
  unfold SV; rewrite evar_rename_iter_FSV, evar_rename_iter_BSV; done.
Qed.

Lemma evar_sub0_not_free x χ ϕ :
  ~ EVarFree x ϕ -> evar_sub0 x χ ϕ = ϕ.
Proof.
  induction ϕ; cbn; intro Hnfree; try done.
  - by case_decide; [subst; contradict Hnfree; constructor |].
  - rewrite IHϕ1, IHϕ2; [done |..]; contradict Hnfree.
    + by apply ef_impl_right.
    + by apply ef_impl_left.
  - by case_decide; [| rewrite IHϕ; [| contradict Hnfree; constructor]].
  - by rewrite IHϕ; [| contradict Hnfree; constructor].
  - rewrite IHϕ1, IHϕ2; [done |..]; contradict Hnfree.
    + by apply ef_app_right.
    + by apply ef_app_left.
Qed.

Lemma evar_sub_rename_not_occurs x y ϕ :
  x <> y -> ¬ EOccursInd x (evar_sub0 x (PEVar y) (evar_rename x y ϕ)).
Proof.
  intros; induction ϕ; cbn. 2-3, 5-7: by inversion 1.
  - by case_decide; inversion 1.
  - case_decide; cbn; rewrite decide_False by done.
    + rewrite evar_sub0_not_free.
      * by contradict IHϕ; inversion IHϕ.
      * by contradict IHϕ; rewrite <- EOccursInd_iff by done; left.
    + by contradict IHϕ; inversion IHϕ.
Qed.

Lemma evar_rename_not_bound_eq to_rename replacement ϕ :
  to_rename <> replacement ->
  to_rename ∉ BEV (evar_rename to_rename replacement ϕ).
Proof.
  induction ϕ; cbn; intros Hne.
  1,2,7: apply not_elem_of_empty.
  - rewrite elem_of_union; intros []; [by apply IHϕ1 | by apply IHϕ2].
  - case_decide; subst; cbn; rewrite elem_of_union, elem_of_singleton.
    + intros [Hs |]; [| done]; contradict Hs.
      rewrite evar_sub0_evar_BEV.
      by apply IHϕ.
    + intros [Hs |]; [| done]; contradict Hs.
      by apply IHϕ.
  - by apply IHϕ.
  - rewrite elem_of_union; intros []; [by apply IHϕ1 | by apply IHϕ2].
Qed.

Lemma evar_rename_not_bound_neq x to_rename replacement ϕ :
  x <> replacement ->
  x ∉ BEV ϕ ->
  x ∉ BEV (evar_rename to_rename replacement ϕ).
Proof.
  induction ϕ; cbn; [done | done |..| done].
  - rewrite !elem_of_union; itauto.
  - case_decide as Hdec; cbn; rewrite !elem_of_union, !elem_of_singleton;
      [setoid_rewrite evar_sub0_evar_BEV |]; itauto.
  - done.
  - rewrite !elem_of_union; itauto.
Qed.

Lemma evar_rename_not_occurs x to_rename replacement ϕ :
  x <> replacement ->
  ~ EOccurs x ϕ ->
  ~ EOccurs x (evar_rename to_rename replacement ϕ).
Proof.
  induction ϕ; cbn; [done | done |..| done].
  - rewrite !EOccurs_impl.
    intros Hnx Hnϕ [|].
    + apply IHϕ1; [done | by contradict Hnϕ; left | done].
    + apply IHϕ2; [done | by contradict Hnϕ; right | done].
  - case_decide as Hdec; rewrite !EOccurs_ex; cycle 1.
    + intros Hnx Hnϕ [|].
      * by contradict Hnϕ; left.
      * by apply IHϕ; [| contradict Hnϕ; right |].
    + subst e; intros Hnx H_nϕ [| Hocc]; [done |].
      eapply evar_sub0_not_occurs; [..| done].
      * apply IHϕ; [| contradict H_nϕ; right]; done.
      * by rewrite EOccursInd_iff; inversion 1.
  - by rewrite !EOccurs_mu.
  - rewrite !EOccurs_app.
    intros Hnx Hnϕ [|].
    + apply IHϕ1; [done | by contradict Hnϕ; left | done].
    + apply IHϕ2; [done | by contradict Hnϕ; right | done].
Qed.

Lemma evar_rename_iter_fresh_not_occurs
  ϕ (x : EVar) (to_rename : list EVar) (to_avoid : EVarSet) :
  ¬ EOccurs x ϕ ->
  x ∉ (fresh_list (length to_rename) to_avoid) ->
  ~ EOccurs x (evar_rename_iter to_rename (fresh_list (length to_rename) to_avoid) ϕ).
Proof.
  revert ϕ x to_avoid; induction to_rename; [done |].
  cbn; intros ϕ x to_avoid Hnocc Hx.
  rewrite elem_of_cons in Hx.
  apply evar_rename_not_occurs, IHto_rename; [| done |];
    contradict Hx; [by left | by right].
Qed.

Lemma evar_rename_iter_fresh_not_bound_to_rename
  ϕ (to_rename to_avoid : EVarSet) :
  to_rename ⊆ to_avoid ->
  forall x, x ∈ to_rename ->
  ~ x ∈ BEV (evar_rename_iter (elements to_rename) (fresh_list (length (elements to_rename)) to_avoid) ϕ).
Proof.
  intros H_incl x Hx.
  apply elem_of_elements in Hx.
  remember (elements to_rename) as l_rename.
  assert (Hincl : Forall (fun x => x ∈ to_avoid) l_rename).
  {
    apply Forall_forall; intros; apply H_incl, elem_of_elements; subst; done.
  }
  clear H_incl to_rename Heql_rename.
  revert ϕ to_avoid Hincl x Hx.
  induction l_rename; intros ϕ to_avoid Hincl x Hx; cbn; [by inversion Hx |].
  apply Forall_cons in Hincl as [Ha Hincl].
  apply elem_of_cons in Hx as [-> | Hx].
  - apply evar_rename_not_bound_eq.
    contradict Ha; subst.
    by apply is_fresh.
  - rewrite Forall_forall in Hincl.
    apply evar_rename_not_bound_neq; [| apply IHl_rename].
    + apply Hincl in Hx; contradict Hx; subst; apply is_fresh; done.
    + apply Forall_forall; intros; apply union_subseteq_r, Hincl; done.
    + done.
Qed.

Lemma evar_rename_iter_fresh_not_bound_to_avoid
  ϕ (to_rename to_avoid : EVarSet) x :
  x ∉ BEV ϕ ->
  x ∈ to_avoid ->
  ~ x ∈ BEV (evar_rename_iter (elements to_rename) (fresh_list (length (elements to_rename)) to_avoid) ϕ).
Proof.
  revert ϕ to_avoid; generalize (elements to_rename) as l_rename.
  induction l_rename; intros ϕ to_avoid Hnx Hx; cbn; [done |].
  apply evar_rename_not_bound_neq.
  - contradict Hx; subst; apply is_fresh; done.
  - apply IHl_rename; [done | by apply union_subseteq_r].
Qed.

Lemma evar_rename_FreeFor x y ϕ (Hxy : x <> y) (Hocc : ~ EOccursInd y ϕ) :
  EFreeForInd x (PEVar y) (evar_rename x y ϕ).
Proof.
  induction ϕ; cbn; intros; cycle 4. 3-5: by constructor.
  - feed specialize IHϕ; [by contradict Hocc; apply eo_mu |].
    by constructor; [| inversion 1].
  - by constructor; [apply IHϕ1 | apply IHϕ2];
      contradict Hocc; [apply eo_app_left | apply eo_app_right].
  - by constructor; [apply IHϕ1 | apply IHϕ2];
      contradict Hocc; [apply eo_impl_left | apply eo_impl_right].
  - feed specialize IHϕ; [by contradict Hocc; apply eo_ex_neq |].
    case_decide; [subst e |].
    + apply EFreeForInd_x_not_occurs.
      cut (~ EOccursInd x (evar_sub0 x (PEVar y) (evar_rename x y ϕ)));
        [rewrite <- !EOccursInd_iff, EOccurs_ex by done; itauto |].
      by apply evar_sub_rename_not_occurs.
    + constructor; [done |].
      by inversion 1; subst; contradict Hocc; constructor.
Qed.

Lemma evar_rename_FreeFor_1 x y z ϕ (Hxy : z <> y) (Hocc : ~ EOccursInd z ϕ) :
  EFreeForInd x (PEVar y) (evar_rename y z ϕ).
Proof.
  apply EFreeForInd_iff, EFreeFor_x_theta_if_not_bound; [| by inversion 1].
  inversion 1; intro; rewrite EVarBound_BEV; apply evar_rename_not_bound_eq; done.
Qed.

Fixpoint svar_sub0 (x : SVar) (delta : Pattern) (p : Pattern) : Pattern :=
  match p with
  | PEVar _ => p
  | PSVar y => if (decide (x = y)) then delta else p
  | POp _ => p
  | PImpl ϕ ψ => PImpl (svar_sub0 x delta ϕ) (svar_sub0 x delta ψ)
  | PApp ϕ ψ => PApp (svar_sub0 x delta ϕ) (svar_sub0 x delta ψ)
  | PEx X ϕ => PEx X (svar_sub0 x delta ϕ)
  | μₚ y ϕ =>  if (decide (x = y)) then p else μₚ y (svar_sub0 x delta ϕ)
  end.

Lemma svar_sub0_svar_BSV x y ϕ :
  BSV (svar_sub0 x (PSVar y) ϕ) ≡ BSV ϕ.
Proof.
  induction ϕ; cbn; [done |..| done].
  - by case_decide.
  - by set_solver.
  - done.
  - by case_decide; set_solver.
  - by set_solver.
Qed.

Lemma svar_sub0_svar_FEV x y ϕ :
  FEV (svar_sub0 x (PSVar y) ϕ) ≡ FEV ϕ.
Proof.
  induction ϕ; cbn.
  - done.
  - by case_decide.
  - set_solver.
  - set_solver.
  - case_decide; set_solver.
  - set_solver.
  - done.
Qed.

Lemma svar_sub0_svar_BEV x y ϕ :
  BEV (svar_sub0 x (PSVar y) ϕ) ≡ BEV ϕ.
Proof.
  induction ϕ; cbn.
  - done.
  - by case_decide.
  - set_solver.
  - set_solver.
  - case_decide; set_solver.
  - set_solver.
  - done.
Qed.

Lemma svar_sub0_svar_EV x y ϕ :
  EV (svar_sub0 x (PSVar y) ϕ) ≡ EV ϕ.
Proof.
  unfold EV; rewrite svar_sub0_svar_FEV, svar_sub0_svar_BEV; done.
Qed.

Lemma svar_sub0_not_free x χ ϕ :
  ~ SVarFree x ϕ -> svar_sub0 x χ ϕ = ϕ.
Proof.
  induction ϕ; cbn; intro Hnfree; try done.
  - by case_decide; [subst; contradict Hnfree; constructor |].
  - by rewrite IHϕ1, IHϕ2; [done |..];
      contradict Hnfree; rewrite SVarFree_FSV by done; cbn;
      rewrite elem_of_union, <- !SVarFree_FSV by done;
      [right | left].
  - by rewrite IHϕ; [| contradict Hnfree; constructor].
  - by case_decide; [| rewrite IHϕ; [| contradict Hnfree; constructor]].
  - by rewrite IHϕ1, IHϕ2; [done |..];
      contradict Hnfree; rewrite SVarFree_FSV by done; cbn;
      rewrite elem_of_union, <- !SVarFree_FSV by done;
      [right | left].
Qed.

Lemma svar_sub0_not_occurs x to_replace replacement ϕ :
  ~ SOccurs x ϕ ->
  ~ SOccurs x replacement ->
  ~ SOccurs x (svar_sub0 to_replace replacement ϕ).
Proof.
  induction ϕ; cbn; try done.
  - by case_decide.
  - rewrite !SOccurs_impl; intros Hnϕ Hnrepl [|].
    + apply IHϕ1; [contradict Hnϕ; left |..]; done.
    + apply IHϕ2; [contradict Hnϕ; right |..]; done.
  - by rewrite !SOccurs_ex.
  - case_decide; rewrite !SOccurs_mu; intros Hnϕ Hnrepl [|].
    + contradict Hnϕ; left; done.
    + contradict Hnϕ; right; done.
    + contradict Hnϕ; left; done.
    + apply IHϕ; [contradict Hnϕ; right |..]; done.
  - rewrite !SOccurs_app; intros Hnϕ Hnrepl [|].
    + apply IHϕ1; [contradict Hnϕ; left |..]; done.
    + apply IHϕ2; [contradict Hnϕ; right |..]; done.
Qed.

Lemma svar_sub0_id x ϕ : svar_sub0 x (PSVar x) ϕ = ϕ.
Proof.
  induction ϕ; cbn. 1,7: done.
  - by case_decide; subst.
  - by rewrite IHϕ1, IHϕ2.
  - by rewrite IHϕ.
  - by rewrite IHϕ; case_decide.
  - by rewrite IHϕ1, IHϕ2.
Qed.

Fixpoint svar_rename (x y : SVar) (p : Pattern) :=
  match p with
  | PEVar _ => p
  | PSVar _ => p
  | POp _ => p
  | PImpl ϕ ψ => PImpl (svar_rename x y ϕ) (svar_rename x y ψ)
  | PApp ϕ ψ => PApp (svar_rename x y ϕ) (svar_rename x y ψ)
  | PEx X ϕ => PEx X (svar_rename x y ϕ)
  | μₚ z ϕ =>
    if (decide (x = z))
      then (μₚ y (svar_sub0 x (PSVar y) (svar_rename x y ϕ)))
      else μₚ z (svar_rename x y ϕ)
  end.

Lemma svar_rename_id x ϕ : svar_rename x x ϕ = ϕ.
Proof.
  induction ϕ; cbn. 1-2,7: done.
  - by rewrite IHϕ1, IHϕ2.
  - by rewrite IHϕ.
  - by rewrite IHϕ, svar_sub0_id; case_decide; subst.
  - by rewrite IHϕ1, IHϕ2.
Qed.

Lemma svar_rename_FEV x y ϕ :
  FEV (svar_rename x y ϕ) ≡ FEV ϕ.
Proof.
  induction ϕ; cbn; [done | done |..| done].
  - set_solver.
  - set_solver.
  - case_decide; cbn; [| done].
    by rewrite svar_sub0_svar_FEV.
  - set_solver.
Qed.

Lemma svar_rename_BEV x y ϕ :
  BEV (svar_rename x y ϕ) ≡ BEV ϕ.
Proof.
  induction ϕ; cbn; [done | done |..| done].
  - set_solver.
  - set_solver.
  - case_decide; cbn; [| done].
    by rewrite svar_sub0_svar_BEV.
  - set_solver.
Qed.

Lemma svar_rename_EV x y ϕ :
  EV (svar_rename x y ϕ) ≡ EV ϕ.
Proof.
  unfold EV; rewrite svar_rename_FEV, svar_rename_BEV; done.
Qed.

Definition svar_rename_iter (xs ys : list SVar) (p : Pattern) : Pattern :=
  foldr (fun (xy : SVar * SVar) (p : Pattern) => svar_rename xy.1 xy.2 p)
    p (zip xs ys).

Lemma svar_rename_iter_FEV (xs ys : list SVar) (ϕ : Pattern) :
  FEV (svar_rename_iter xs ys ϕ) ≡ FEV ϕ.
Proof.
  revert ys ϕ.
  induction xs; [done |].
  intros [|b ys] ϕ; [done |]; cbn.
  rewrite svar_rename_FEV.
  by apply IHxs.
Qed.

Lemma svar_rename_iter_BEV (xs ys : list SVar) (ϕ : Pattern) :
  BEV (svar_rename_iter xs ys ϕ) ≡ BEV ϕ.
Proof.
  revert ys ϕ.
  induction xs; [done |].
  intros [|b ys] ϕ; [done |]; cbn.
  rewrite svar_rename_BEV.
  by apply IHxs.
Qed.

Lemma svar_rename_iter_EV (xs ys : list SVar) (ϕ : Pattern) :
  EV (svar_rename_iter xs ys ϕ) ≡ EV ϕ.
Proof.
  unfold EV; rewrite svar_rename_iter_FEV, svar_rename_iter_BEV; done.
Qed.

Lemma svar_sub_rename_not_occurs x y ϕ :
  x <> y -> ¬ SOccursInd x (svar_sub0 x (PSVar y) (svar_rename x y ϕ)).
Proof.
  intros; induction ϕ; cbn. 1,3-4, 6,7: by inversion 1.
  - by case_decide; inversion 1.
  - case_decide; cbn; rewrite decide_False by done.
    + rewrite svar_sub0_not_free.
      * by contradict IHϕ; inversion IHϕ.
      * by contradict IHϕ; rewrite <- SOccursInd_iff by done; left.
    + by contradict IHϕ; inversion IHϕ.
Qed.

Lemma svar_rename_not_bound_eq to_rename replacement ϕ :
  to_rename <> replacement ->
  to_rename ∉ BSV (svar_rename to_rename replacement ϕ).
Proof.
  induction ϕ; cbn; intros Hne.
  1,2,7: apply not_elem_of_empty.
  - rewrite elem_of_union; intros []; [by apply IHϕ1 | by apply IHϕ2].
  - by apply IHϕ.
  - case_decide; subst; cbn; rewrite elem_of_union, elem_of_singleton.
    + intros [Hs |]; [| done]; contradict Hs.
      rewrite svar_sub0_svar_BSV.
      by apply IHϕ.
    + intros [Hs |]; [| done]; contradict Hs.
      by apply IHϕ.
  - rewrite elem_of_union; intros []; [by apply IHϕ1 | by apply IHϕ2].
Qed.

Lemma svar_rename_not_bound_neq x to_rename replacement ϕ :
  x <> replacement ->
  x ∉ BSV ϕ ->
  x ∉ BSV (svar_rename to_rename replacement ϕ).
Proof.
  induction ϕ; cbn; [done | done |..| done].
  - rewrite !elem_of_union; itauto.
  - done.
  - case_decide as Hdec; cbn; rewrite !elem_of_union, !elem_of_singleton;
      [setoid_rewrite svar_sub0_svar_BSV |]; itauto.
  - rewrite !elem_of_union; itauto.
Qed.

Lemma svar_rename_not_occurs x to_rename replacement ϕ :
  x <> replacement ->
  ~ SOccurs x ϕ ->
  ~ SOccurs x (svar_rename to_rename replacement ϕ).
Proof.
  induction ϕ; cbn; [done | done |..| done].
  - rewrite !SOccurs_impl.
    intros Hnx Hnϕ [|].
    + apply IHϕ1; [done | by contradict Hnϕ; left | done].
    + apply IHϕ2; [done | by contradict Hnϕ; right | done].
  - by rewrite !SOccurs_ex.
  - case_decide as Hdec; rewrite !SOccurs_mu; cycle 1.
    + intros Hnx Hnϕ [|].
      * by contradict Hnϕ; left.
      * by apply IHϕ; [| contradict Hnϕ; right |].
    + subst s; intros Hnx H_nϕ [| Hocc]; [done |].
      eapply svar_sub0_not_occurs; [..| done].
      * apply IHϕ; [| contradict H_nϕ; right]; done.
      * by rewrite SOccursInd_iff; inversion 1.
  - rewrite !SOccurs_app.
    intros Hnx Hnϕ [|].
    + apply IHϕ1; [done | by contradict Hnϕ; left | done].
    + apply IHϕ2; [done | by contradict Hnϕ; right | done].
Qed.

Lemma svar_rename_iter_fresh_not_occurs
  ϕ (x : SVar) (to_rename : list SVar) (to_avoid : SVarSet) :
  ¬ SOccurs x ϕ ->
  x ∉ (fresh_list (length to_rename) to_avoid) ->
  ~ SOccurs x (svar_rename_iter to_rename (fresh_list (length to_rename) to_avoid) ϕ).
Proof.
  revert ϕ x to_avoid; induction to_rename; [done |].
  cbn; intros ϕ x to_avoid Hnocc Hx.
  rewrite elem_of_cons in Hx.
  apply svar_rename_not_occurs, IHto_rename; [| done |];
    contradict Hx; [by left | by right].
Qed.

Lemma svar_rename_iter_fresh_not_bound_to_rename
  ϕ (to_rename to_avoid : SVarSet) :
  to_rename ⊆ to_avoid ->
  forall x, x ∈ to_rename ->
  ~ x ∈ BSV (svar_rename_iter (elements to_rename) (fresh_list (length (elements to_rename)) to_avoid) ϕ).
Proof.
  unfold size, set_size; cbn.
  intros H_incl x Hx.
  apply elem_of_elements in Hx.
  remember (elements to_rename) as l_rename.
  assert (Hincl : Forall (fun x => x ∈ to_avoid) l_rename).
  {
    apply Forall_forall; intros; apply H_incl, elem_of_elements; subst; done.
  }
  clear H_incl to_rename Heql_rename.
  revert ϕ to_avoid Hincl x Hx.
  induction l_rename; intros ϕ to_avoid Hincl x Hx; cbn; [by inversion Hx |].
  apply Forall_cons in Hincl as [Ha Hincl].
  apply elem_of_cons in Hx as [-> | Hx].
  - apply svar_rename_not_bound_eq.
    contradict Ha; subst.
    by apply is_fresh.
  - rewrite Forall_forall in Hincl.
    apply svar_rename_not_bound_neq; [| apply IHl_rename].
    + apply Hincl in Hx; contradict Hx; subst; apply is_fresh; done.
    + apply Forall_forall; intros; apply union_subseteq_r, Hincl; done.
    + done.
Qed.

Lemma svar_rename_iter_fresh_not_bound_to_avoid
  ϕ (to_rename to_avoid : SVarSet) x :
  x ∉ BSV ϕ ->
  x ∈ to_avoid ->
  ~ x ∈ BSV (svar_rename_iter (elements to_rename) (fresh_list (length (elements to_rename)) to_avoid) ϕ).
Proof.
  revert ϕ to_avoid; generalize (elements to_rename) as l_rename.
  induction l_rename; intros ϕ to_avoid Hnx Hx; cbn; [done |].
  apply svar_rename_not_bound_neq.
  - contradict Hx; subst; apply is_fresh; done.
  - apply IHl_rename; [done | by apply union_subseteq_r].
Qed.

Lemma svar_rename_FreeFor x y ϕ (Hxy : x <> y) (Hocc : ~ SOccursInd y ϕ) :
  SFreeForInd x (PSVar y) (svar_rename x y ϕ).
Proof.
  induction ϕ; cbn; intros; cycle 5. 2-4: by constructor.
  - by constructor; [apply IHϕ1 | apply IHϕ2];
      contradict Hocc; [apply so_app_left | apply so_app_right].
  - by constructor; [apply IHϕ1 | apply IHϕ2];
      contradict Hocc; [apply so_impl_left | apply so_impl_right].
  - feed specialize IHϕ; [by contradict Hocc; apply so_ex |].
    by constructor; [| inversion 1].
  - feed specialize IHϕ; [by contradict Hocc; apply so_mu_neq |].
    case_decide; [subst s |].
    + apply SFreeForInd_x_not_occurs.
      cut (~ SOccursInd x (svar_sub0 x (PSVar y) (svar_rename x y ϕ)));
        [rewrite <- !SOccursInd_iff, SOccurs_mu by done; itauto |].
      by apply svar_sub_rename_not_occurs.
    + constructor; [done |].
      by inversion 1; subst; contradict Hocc; constructor.
Qed.

Definition esubst (ϕ : Pattern) (x : EVar) (ψ : Pattern) :=
  let ϕ_ψ_evars := EV ϕ ∪ EV ψ : EVarSet in
  let ϕ_ψ_svars := SV ϕ ∪ SV ψ : SVarSet in
  let bound_ϕ_ψ_evar_set := BEV ϕ ∩ EV ψ : EVarSet in
  let bound_ϕ_ψ_evars := elements bound_ϕ_ψ_evar_set in
  let bound_ϕ_ψ_svar_set := BSV ϕ ∩ SV ψ  : SVarSet in
  let bound_ϕ_ψ_svars := elements bound_ϕ_ψ_svar_set in
  let fresh_evars := fresh_list (length bound_ϕ_ψ_evars) ϕ_ψ_evars in
  let fresh_svars := fresh_list (length bound_ϕ_ψ_svars) ϕ_ψ_svars in
  let etheta := evar_rename_iter bound_ϕ_ψ_evars fresh_evars ϕ in
  let theta := svar_rename_iter bound_ϕ_ψ_svars fresh_svars etheta in
  evar_sub0 x ψ theta.

Definition ssubst (ϕ : Pattern) (x : SVar) (ψ : Pattern) :=
  let ϕ_ψ_evars := EV ϕ ∪ EV ψ : EVarSet in
  let ϕ_ψ_svars := SV ϕ ∪ SV ψ : SVarSet in
  let bound_ϕ_ψ_evar_set := BEV ϕ ∩ EV ψ : EVarSet in
  let bound_ϕ_ψ_evars := elements bound_ϕ_ψ_evar_set in
  let bound_ϕ_ψ_svar_set := BSV ϕ ∩ SV ψ  : SVarSet in
  let bound_ϕ_ψ_svars := elements bound_ϕ_ψ_svar_set in
  let fresh_evars := fresh_list (length bound_ϕ_ψ_evars) ϕ_ψ_evars in
  let fresh_svars := fresh_list (length bound_ϕ_ψ_svars) ϕ_ψ_svars in
  let etheta := evar_rename_iter bound_ϕ_ψ_evars fresh_evars ϕ in
  let theta := svar_rename_iter bound_ϕ_ψ_svars fresh_svars etheta in
  svar_sub0 x ψ theta.

Definition νₚ (X : SVar) (ϕ : Pattern) :=
  pNeg (μₚ X (pNeg (svar_sub0 X (pNeg (PSVar X)) ϕ))).

End sec_substitution.
