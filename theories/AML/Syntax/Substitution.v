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
  | PImpl phi psi => PImpl (evar_sub0 x delta phi) (evar_sub0 x delta psi)
  | PApp phi psi => PApp (evar_sub0 x delta phi) (evar_sub0 x delta psi)
  | PEx y phi =>  if (decide (x = y)) then p else PEx y (evar_sub0 x delta phi)
  | PMu X phi => PMu X (evar_sub0 x delta phi)
  end.

Lemma evar_sub0_evar_BEV x y phi :
  BEV (evar_sub0 x (PEVar y) phi) ≡ BEV phi.
Proof.
  induction phi; cbn; [| done |..| done].
  - by case_decide.
  - by set_solver.
  - by case_decide; set_solver.
  - done.
  - by set_solver.
Qed.

Lemma evar_sub0_evar_FSV x y phi :
  FSV (evar_sub0 x (PEVar y) phi) ≡ FSV phi.
Proof.
  induction phi; cbn.
  - by case_decide.
  - done.
  - set_solver.
  - case_decide; set_solver.
  - set_solver.
  - set_solver.
  - done.
Qed.

Lemma evar_sub0_evar_BSV x y phi :
  BSV (evar_sub0 x (PEVar y) phi) ≡ BSV phi.
Proof.
  induction phi; cbn.
  - by case_decide.
  - done.
  - set_solver.
  - case_decide; set_solver.
  - set_solver.
  - set_solver.
  - done.
Qed.

Lemma evar_sub0_evar_SV x y phi :
  SV (evar_sub0 x (PEVar y) phi) ≡ SV phi.
Proof.
  unfold SV; rewrite evar_sub0_evar_FSV, evar_sub0_evar_BSV; done.
Qed.

Lemma evar_sub0_not_occurs x to_replace replacement phi :
  ~ EOccurs x phi ->
  ~ EOccurs x replacement ->
  ~ EOccurs x (evar_sub0 to_replace replacement phi).
Proof.
  induction phi; cbn; try done.
  - by case_decide.
  - rewrite !EOccurs_impl; intros Hnphi Hnrepl [|].
    + apply IHphi1; [contradict Hnphi; left |..]; done.
    + apply IHphi2; [contradict Hnphi; right |..]; done.
  - case_decide; rewrite !EOccurs_ex; intros Hnphi Hnrepl [|].
    + contradict Hnphi; left; done.
    + contradict Hnphi; right; done.
    + contradict Hnphi; left; done.
    + apply IHphi; [contradict Hnphi; right |..]; done.
  - by rewrite !EOccurs_mu.
  - rewrite !EOccurs_app; intros Hnphi Hnrepl [|].
    + apply IHphi1; [contradict Hnphi; left |..]; done.
    + apply IHphi2; [contradict Hnphi; right |..]; done.
Qed.

Lemma evar_sub0_id x phi : evar_sub0 x (PEVar x) phi = phi.
Proof.
  induction phi; cbn. 2,7: done.
  - by case_decide; subst.
  - by rewrite IHphi1, IHphi2.
  - by rewrite IHphi; case_decide.
  - by rewrite IHphi.
  - by rewrite IHphi1, IHphi2.
Qed.

Fixpoint evar_rename (x y : EVar) (p : Pattern) : Pattern :=
  match p with
  | PEVar _ => p
  | PSVar _ => p
  | POp _ => p
  | PImpl phi psi => PImpl (evar_rename x y phi) (evar_rename x y psi)
  | PApp phi psi => PApp (evar_rename x y phi) (evar_rename x y psi)
  | PEx z phi =>
    if (decide (x = z))
      then (PEx y (evar_sub0 x (PEVar y) (evar_rename x y phi)))
      else PEx z (evar_rename x y phi)
  | PMu X phi => PMu X (evar_rename x y phi)
  end.

Lemma evar_rename_id x phi : evar_rename x x phi = phi.
Proof.
  induction phi; cbn. 1-2,7: done.
  - by rewrite IHphi1, IHphi2.
  - by rewrite IHphi, evar_sub0_id; case_decide; subst.
  - by rewrite IHphi.
  - by rewrite IHphi1, IHphi2.
Qed.

Lemma evar_rename_FSV x y phi :
  FSV (evar_rename x y phi) ≡ FSV phi.
Proof.
  induction phi; cbn; [done | done |..| done].
  - set_solver.
  - case_decide; cbn; [| done].
    by rewrite evar_sub0_evar_FSV.
  - set_solver.
  - set_solver.
Qed.

Lemma evar_rename_BSV x y phi :
  BSV (evar_rename x y phi) ≡ BSV phi.
Proof.
  induction phi; cbn; [done | done |..| done].
  - set_solver.
  - case_decide; cbn; [| done].
    by rewrite evar_sub0_evar_BSV.
  - set_solver.
  - set_solver.
Qed.

Lemma evar_rename_SV x y phi :
  SV (evar_rename x y phi) ≡ SV phi.
Proof.
  unfold SV; rewrite evar_rename_FSV, evar_rename_BSV; done.
Qed.

Definition evar_rename_iter (xs ys : list EVar) (p : Pattern) : Pattern :=
  foldr (fun (xy : EVar * EVar) (p : Pattern) => evar_rename xy.1 xy.2 p)
    p (zip xs ys).

Lemma evar_rename_iter_FSV (xs ys : list EVar) (phi : Pattern) :
  FSV (evar_rename_iter xs ys phi) ≡ FSV phi.
Proof.
  revert ys phi.
  induction xs; [done |].
  intros [|b ys] phi; [done |]; cbn.
  rewrite evar_rename_FSV.
  by apply IHxs.
Qed.

Lemma evar_rename_iter_BSV (xs ys : list EVar) (phi : Pattern) :
  BSV (evar_rename_iter xs ys phi) ≡ BSV phi.
Proof.
  revert ys phi.
  induction xs; [done |].
  intros [|b ys] phi; [done |]; cbn.
  rewrite evar_rename_BSV.
  by apply IHxs.
Qed.

Lemma evar_rename_iter_SV (xs ys : list EVar) (phi : Pattern) :
  SV (evar_rename_iter xs ys phi) ≡ SV phi.
Proof.
  unfold SV; rewrite evar_rename_iter_FSV, evar_rename_iter_BSV; done.
Qed.

Lemma evar_sub0_not_free x chi phi :
  ~ EVarFree x phi -> evar_sub0 x chi phi = phi.
Proof.
  induction phi; cbn; intro Hnfree; try done.
  - by case_decide; [subst; contradict Hnfree; constructor |].
  - rewrite IHphi1, IHphi2; [done |..]; contradict Hnfree.
    + by apply ef_impl_right.
    + by apply ef_impl_left.
  - by case_decide; [| rewrite IHphi; [| contradict Hnfree; constructor]].
  - by rewrite IHphi; [| contradict Hnfree; constructor].
  - rewrite IHphi1, IHphi2; [done |..]; contradict Hnfree.
    + by apply ef_app_right.
    + by apply ef_app_left.
Qed.

Lemma evar_sub_rename_not_occurs x y phi :
  x <> y -> ¬ EOccursInd x (evar_sub0 x (PEVar y) (evar_rename x y phi)).
Proof.
  intros; induction phi; cbn. 2-3, 5-7: by inversion 1.
  - by case_decide; inversion 1.
  - case_decide; cbn; rewrite decide_False by done.
    + rewrite evar_sub0_not_free.
      * by contradict IHphi; inversion IHphi.
      * by contradict IHphi; rewrite <- EOccursInd_iff by done; left.
    + by contradict IHphi; inversion IHphi.
Qed.

Lemma evar_rename_not_bound_eq to_rename replacement phi :
  to_rename <> replacement ->
  to_rename ∉ BEV (evar_rename to_rename replacement phi).
Proof.
  induction phi; cbn; intros Hne.
  1,2,7: apply not_elem_of_empty.
  - rewrite elem_of_union; intros []; [by apply IHphi1 | by apply IHphi2].
  - case_decide; subst; cbn; rewrite elem_of_union, elem_of_singleton.
    + intros [Hs |]; [| done]; contradict Hs.
      rewrite evar_sub0_evar_BEV.
      by apply IHphi.
    + intros [Hs |]; [| done]; contradict Hs.
      by apply IHphi.
  - by apply IHphi.
  - rewrite elem_of_union; intros []; [by apply IHphi1 | by apply IHphi2].
Qed.

Lemma evar_rename_not_bound_neq x to_rename replacement phi :
  x <> replacement ->
  x ∉ BEV phi ->
  x ∉ BEV (evar_rename to_rename replacement phi).
Proof.
  induction phi; cbn; [done | done |..| done].
  - rewrite !elem_of_union; itauto.
  - case_decide as Hdec; cbn; rewrite !elem_of_union, !elem_of_singleton;
      [setoid_rewrite evar_sub0_evar_BEV |]; itauto.
  - done.
  - rewrite !elem_of_union; itauto.
Qed.

Lemma evar_rename_not_occurs x to_rename replacement phi :
  x <> replacement ->
  ~ EOccurs x phi ->
  ~ EOccurs x (evar_rename to_rename replacement phi).
Proof.
  induction phi; cbn; [done | done |..| done].
  - rewrite !EOccurs_impl.
    intros Hnx Hnphi [|].
    + apply IHphi1; [done | by contradict Hnphi; left | done].
    + apply IHphi2; [done | by contradict Hnphi; right | done].
  - case_decide as Hdec; rewrite !EOccurs_ex; cycle 1.
    + intros Hnx Hnphi [|].
      * by contradict Hnphi; left.
      * by apply IHphi; [| contradict Hnphi; right |].
    + subst e; intros Hnx H_nphi [| Hocc]; [done |].
      eapply evar_sub0_not_occurs; [..| done].
      * apply IHphi; [| contradict H_nphi; right]; done.
      * by rewrite EOccursInd_iff; inversion 1.
  - by rewrite !EOccurs_mu.
  - rewrite !EOccurs_app.
    intros Hnx Hnphi [|].
    + apply IHphi1; [done | by contradict Hnphi; left | done].
    + apply IHphi2; [done | by contradict Hnphi; right | done].
Qed.

Lemma evar_rename_iter_fresh_not_occurs
  phi (x : EVar) (to_rename : list EVar) (to_avoid : EVarSet) :
  ¬ EOccurs x phi ->
  x ∉ (fresh_list (length to_rename) to_avoid) ->
  ~ EOccurs x (evar_rename_iter to_rename (fresh_list (length to_rename) to_avoid) phi).
Proof.
  revert phi x to_avoid; induction to_rename; [done |].
  cbn; intros phi x to_avoid Hnocc Hx.
  rewrite elem_of_cons in Hx.
  apply evar_rename_not_occurs, IHto_rename; [| done |];
    contradict Hx; [by left | by right].
Qed.

Lemma evar_rename_iter_fresh_not_bound_to_rename
  phi (to_rename to_avoid : EVarSet) :
  to_rename ⊆ to_avoid ->
  forall x, x ∈ to_rename ->
  ~ x ∈ BEV (evar_rename_iter (elements to_rename) (fresh_list (length (elements to_rename)) to_avoid) phi).
Proof.
  intros H_incl x Hx.
  apply elem_of_elements in Hx.
  remember (elements to_rename) as l_rename.
  assert (Hincl : Forall (fun x => x ∈ to_avoid) l_rename).
  {
    apply Forall_forall; intros; apply H_incl, elem_of_elements; subst; done.
  }
  clear H_incl to_rename Heql_rename.
  revert phi to_avoid Hincl x Hx.
  induction l_rename; intros phi to_avoid Hincl x Hx; cbn; [by inversion Hx |].
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
  phi (to_rename to_avoid : EVarSet) x :
  x ∉ BEV phi ->
  x ∈ to_avoid ->
  ~ x ∈ BEV (evar_rename_iter (elements to_rename) (fresh_list (length (elements to_rename)) to_avoid) phi).
Proof.
  revert phi to_avoid; generalize (elements to_rename) as l_rename.
  induction l_rename; intros phi to_avoid Hnx Hx; cbn; [done |].
  apply evar_rename_not_bound_neq.
  - contradict Hx; subst; apply is_fresh; done.
  - apply IHl_rename; [done | by apply union_subseteq_r].
Qed.

Lemma evar_rename_FreeFor x y phi (Hxy : x <> y) (Hocc : ~ EOccursInd y phi) :
  EFreeForInd x (PEVar y) (evar_rename x y phi).
Proof.
  induction phi; cbn; intros; cycle 4. 3-5: by constructor.
  - feed specialize IHphi; [by contradict Hocc; apply eo_mu |].
    by constructor; [| inversion 1].
  - by constructor; [apply IHphi1 | apply IHphi2];
      contradict Hocc; [apply eo_app_left | apply eo_app_right].
  - by constructor; [apply IHphi1 | apply IHphi2];
      contradict Hocc; [apply eo_impl_left | apply eo_impl_right].
  - feed specialize IHphi; [by contradict Hocc; apply eo_ex_neq |].
    case_decide; [subst e |].
    + apply EFreeForInd_x_not_occurs.
      cut (~ EOccursInd x (evar_sub0 x (PEVar y) (evar_rename x y phi)));
        [rewrite <- !EOccursInd_iff, EOccurs_ex by done; itauto |].
      by apply evar_sub_rename_not_occurs.
    + constructor; [done |].
      by inversion 1; subst; contradict Hocc; constructor.
Qed.

Lemma evar_rename_FreeFor_1 x y z phi (Hxy : z <> y) (Hocc : ~ EOccursInd z phi) :
  EFreeForInd x (PEVar y) (evar_rename y z phi).
Proof.
  apply EFreeForInd_iff, EFreeFor_x_theta_if_not_bound; [| by inversion 1].
  inversion 1; intro; rewrite EVarBound_BEV; apply evar_rename_not_bound_eq; done.
Qed.

Fixpoint svar_sub0 (x : SVar) (delta : Pattern) (p : Pattern) : Pattern :=
  match p with
  | PEVar _ => p
  | PSVar y => if (decide (x = y)) then delta else p
  | POp _ => p
  | PImpl phi psi => PImpl (svar_sub0 x delta phi) (svar_sub0 x delta psi)
  | PApp phi psi => PApp (svar_sub0 x delta phi) (svar_sub0 x delta psi)
  | PEx X phi => PEx X (svar_sub0 x delta phi)
  | PMu y phi =>  if (decide (x = y)) then p else PMu y (svar_sub0 x delta phi)
  end.

Lemma svar_sub0_svar_BSV x y phi :
  BSV (svar_sub0 x (PSVar y) phi) ≡ BSV phi.
Proof.
  induction phi; cbn; [done |..| done].
  - by case_decide.
  - by set_solver.
  - done.
  - by case_decide; set_solver.
  - by set_solver.
Qed.

Lemma svar_sub0_svar_FEV x y phi :
  FEV (svar_sub0 x (PSVar y) phi) ≡ FEV phi.
Proof.
  induction phi; cbn.
  - done.
  - by case_decide.
  - set_solver.
  - set_solver.
  - case_decide; set_solver.
  - set_solver.
  - done.
Qed.

Lemma svar_sub0_svar_BEV x y phi :
  BEV (svar_sub0 x (PSVar y) phi) ≡ BEV phi.
Proof.
  induction phi; cbn.
  - done.
  - by case_decide.
  - set_solver.
  - set_solver.
  - case_decide; set_solver.
  - set_solver.
  - done.
Qed.

Lemma svar_sub0_svar_EV x y phi :
  EV (svar_sub0 x (PSVar y) phi) ≡ EV phi.
Proof.
  unfold EV; rewrite svar_sub0_svar_FEV, svar_sub0_svar_BEV; done.
Qed.

Lemma svar_sub0_not_free x chi phi :
  ~ SVarFree x phi -> svar_sub0 x chi phi = phi.
Proof.
  induction phi; cbn; intro Hnfree; try done.
  - by case_decide; [subst; contradict Hnfree; constructor |].
  - by rewrite IHphi1, IHphi2; [done |..];
      contradict Hnfree; rewrite SVarFree_FSV by done; cbn;
      rewrite elem_of_union, <- !SVarFree_FSV by done;
      [right | left].
  - by rewrite IHphi; [| contradict Hnfree; constructor].
  - by case_decide; [| rewrite IHphi; [| contradict Hnfree; constructor]].
  - by rewrite IHphi1, IHphi2; [done |..];
      contradict Hnfree; rewrite SVarFree_FSV by done; cbn;
      rewrite elem_of_union, <- !SVarFree_FSV by done;
      [right | left].
Qed.

Lemma svar_sub0_not_occurs x to_replace replacement phi :
  ~ SOccurs x phi ->
  ~ SOccurs x replacement ->
  ~ SOccurs x (svar_sub0 to_replace replacement phi).
Proof.
  induction phi; cbn; try done.
  - by case_decide.
  - rewrite !SOccurs_impl; intros Hnphi Hnrepl [|].
    + apply IHphi1; [contradict Hnphi; left |..]; done.
    + apply IHphi2; [contradict Hnphi; right |..]; done.
  - by rewrite !SOccurs_ex.
  - case_decide; rewrite !SOccurs_mu; intros Hnphi Hnrepl [|].
    + contradict Hnphi; left; done.
    + contradict Hnphi; right; done.
    + contradict Hnphi; left; done.
    + apply IHphi; [contradict Hnphi; right |..]; done.
  - rewrite !SOccurs_app; intros Hnphi Hnrepl [|].
    + apply IHphi1; [contradict Hnphi; left |..]; done.
    + apply IHphi2; [contradict Hnphi; right |..]; done.
Qed.

Lemma svar_sub0_id x phi : svar_sub0 x (PSVar x) phi = phi.
Proof.
  induction phi; cbn. 1,7: done.
  - by case_decide; subst.
  - by rewrite IHphi1, IHphi2.
  - by rewrite IHphi.
  - by rewrite IHphi; case_decide.
  - by rewrite IHphi1, IHphi2.
Qed.

Fixpoint svar_rename (x y : SVar) (p : Pattern) :=
  match p with
  | PEVar _ => p
  | PSVar _ => p
  | POp _ => p
  | PImpl phi psi => PImpl (svar_rename x y phi) (svar_rename x y psi)
  | PApp phi psi => PApp (svar_rename x y phi) (svar_rename x y psi)
  | PEx X phi => PEx X (svar_rename x y phi)
  | PMu z phi =>
    if (decide (x = z))
      then (PMu y (svar_sub0 x (PSVar y) (svar_rename x y phi)))
      else PMu z (svar_rename x y phi)
  end.

Lemma svar_rename_id x phi : svar_rename x x phi = phi.
Proof.
  induction phi; cbn. 1-2,7: done.
  - by rewrite IHphi1, IHphi2.
  - by rewrite IHphi.
  - by rewrite IHphi, svar_sub0_id; case_decide; subst.
  - by rewrite IHphi1, IHphi2.
Qed.

Lemma svar_rename_FEV x y phi :
  FEV (svar_rename x y phi) ≡ FEV phi.
Proof.
  induction phi; cbn; [done | done |..| done].
  - set_solver.
  - set_solver.
  - case_decide; cbn; [| done].
    by rewrite svar_sub0_svar_FEV.
  - set_solver.
Qed.

Lemma svar_rename_BEV x y phi :
  BEV (svar_rename x y phi) ≡ BEV phi.
Proof.
  induction phi; cbn; [done | done |..| done].
  - set_solver.
  - set_solver.
  - case_decide; cbn; [| done].
    by rewrite svar_sub0_svar_BEV.
  - set_solver.
Qed.

Lemma svar_rename_EV x y phi :
  EV (svar_rename x y phi) ≡ EV phi.
Proof.
  unfold EV; rewrite svar_rename_FEV, svar_rename_BEV; done.
Qed.

Definition svar_rename_iter (xs ys : list SVar) (p : Pattern) : Pattern :=
  foldr (fun (xy : SVar * SVar) (p : Pattern) => svar_rename xy.1 xy.2 p)
    p (zip xs ys).

Lemma svar_rename_iter_FEV (xs ys : list SVar) (phi : Pattern) :
  FEV (svar_rename_iter xs ys phi) ≡ FEV phi.
Proof.
  revert ys phi.
  induction xs; [done |].
  intros [|b ys] phi; [done |]; cbn.
  rewrite svar_rename_FEV.
  by apply IHxs.
Qed.

Lemma svar_rename_iter_BEV (xs ys : list SVar) (phi : Pattern) :
  BEV (svar_rename_iter xs ys phi) ≡ BEV phi.
Proof.
  revert ys phi.
  induction xs; [done |].
  intros [|b ys] phi; [done |]; cbn.
  rewrite svar_rename_BEV.
  by apply IHxs.
Qed.

Lemma svar_rename_iter_EV (xs ys : list SVar) (phi : Pattern) :
  EV (svar_rename_iter xs ys phi) ≡ EV phi.
Proof.
  unfold EV; rewrite svar_rename_iter_FEV, svar_rename_iter_BEV; done.
Qed.

Lemma svar_sub_rename_not_occurs x y phi :
  x <> y -> ¬ SOccursInd x (svar_sub0 x (PSVar y) (svar_rename x y phi)).
Proof.
  intros; induction phi; cbn. 1,3-4, 6,7: by inversion 1.
  - by case_decide; inversion 1.
  - case_decide; cbn; rewrite decide_False by done.
    + rewrite svar_sub0_not_free.
      * by contradict IHphi; inversion IHphi.
      * by contradict IHphi; rewrite <- SOccursInd_iff by done; left.
    + by contradict IHphi; inversion IHphi.
Qed.

Lemma svar_rename_not_bound_eq to_rename replacement phi :
  to_rename <> replacement ->
  to_rename ∉ BSV (svar_rename to_rename replacement phi).
Proof.
  induction phi; cbn; intros Hne.
  1,2,7: apply not_elem_of_empty.
  - rewrite elem_of_union; intros []; [by apply IHphi1 | by apply IHphi2].
  - by apply IHphi.
  - case_decide; subst; cbn; rewrite elem_of_union, elem_of_singleton.
    + intros [Hs |]; [| done]; contradict Hs.
      rewrite svar_sub0_svar_BSV.
      by apply IHphi.
    + intros [Hs |]; [| done]; contradict Hs.
      by apply IHphi.
  - rewrite elem_of_union; intros []; [by apply IHphi1 | by apply IHphi2].
Qed.

Lemma svar_rename_not_bound_neq x to_rename replacement phi :
  x <> replacement ->
  x ∉ BSV phi ->
  x ∉ BSV (svar_rename to_rename replacement phi).
Proof.
  induction phi; cbn; [done | done |..| done].
  - rewrite !elem_of_union; itauto.
  - done.
  - case_decide as Hdec; cbn; rewrite !elem_of_union, !elem_of_singleton;
      [setoid_rewrite svar_sub0_svar_BSV |]; itauto.
  - rewrite !elem_of_union; itauto.
Qed.

Lemma svar_rename_not_occurs x to_rename replacement phi :
  x <> replacement ->
  ~ SOccurs x phi ->
  ~ SOccurs x (svar_rename to_rename replacement phi).
Proof.
  induction phi; cbn; [done | done |..| done].
  - rewrite !SOccurs_impl.
    intros Hnx Hnphi [|].
    + apply IHphi1; [done | by contradict Hnphi; left | done].
    + apply IHphi2; [done | by contradict Hnphi; right | done].
  - by rewrite !SOccurs_ex.
  - case_decide as Hdec; rewrite !SOccurs_mu; cycle 1.
    + intros Hnx Hnphi [|].
      * by contradict Hnphi; left.
      * by apply IHphi; [| contradict Hnphi; right |].
    + subst s; intros Hnx H_nphi [| Hocc]; [done |].
      eapply svar_sub0_not_occurs; [..| done].
      * apply IHphi; [| contradict H_nphi; right]; done.
      * by rewrite SOccursInd_iff; inversion 1.
  - rewrite !SOccurs_app.
    intros Hnx Hnphi [|].
    + apply IHphi1; [done | by contradict Hnphi; left | done].
    + apply IHphi2; [done | by contradict Hnphi; right | done].
Qed.

Lemma svar_rename_iter_fresh_not_occurs
  phi (x : SVar) (to_rename : list SVar) (to_avoid : SVarSet) :
  ¬ SOccurs x phi ->
  x ∉ (fresh_list (length to_rename) to_avoid) ->
  ~ SOccurs x (svar_rename_iter to_rename (fresh_list (length to_rename) to_avoid) phi).
Proof.
  revert phi x to_avoid; induction to_rename; [done |].
  cbn; intros phi x to_avoid Hnocc Hx.
  rewrite elem_of_cons in Hx.
  apply svar_rename_not_occurs, IHto_rename; [| done |];
    contradict Hx; [by left | by right].
Qed.

Lemma svar_rename_iter_fresh_not_bound_to_rename
  phi (to_rename to_avoid : SVarSet) :
  to_rename ⊆ to_avoid ->
  forall x, x ∈ to_rename ->
  ~ x ∈ BSV (svar_rename_iter (elements to_rename) (fresh_list (length (elements to_rename)) to_avoid) phi).
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
  revert phi to_avoid Hincl x Hx.
  induction l_rename; intros phi to_avoid Hincl x Hx; cbn; [by inversion Hx |].
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
  phi (to_rename to_avoid : SVarSet) x :
  x ∉ BSV phi ->
  x ∈ to_avoid ->
  ~ x ∈ BSV (svar_rename_iter (elements to_rename) (fresh_list (length (elements to_rename)) to_avoid) phi).
Proof.
  revert phi to_avoid; generalize (elements to_rename) as l_rename.
  induction l_rename; intros phi to_avoid Hnx Hx; cbn; [done |].
  apply svar_rename_not_bound_neq.
  - contradict Hx; subst; apply is_fresh; done.
  - apply IHl_rename; [done | by apply union_subseteq_r].
Qed.

Lemma svar_rename_FreeFor x y phi (Hxy : x <> y) (Hocc : ~ SOccursInd y phi) :
  SFreeForInd x (PSVar y) (svar_rename x y phi).
Proof.
  induction phi; cbn; intros; cycle 5. 2-4: by constructor.
  - by constructor; [apply IHphi1 | apply IHphi2];
      contradict Hocc; [apply so_app_left | apply so_app_right].
  - by constructor; [apply IHphi1 | apply IHphi2];
      contradict Hocc; [apply so_impl_left | apply so_impl_right].
  - feed specialize IHphi; [by contradict Hocc; apply so_ex |].
    by constructor; [| inversion 1].
  - feed specialize IHphi; [by contradict Hocc; apply so_mu_neq |].
    case_decide; [subst s |].
    + apply SFreeForInd_x_not_occurs.
      cut (~ SOccursInd x (svar_sub0 x (PSVar y) (svar_rename x y phi)));
        [rewrite <- !SOccursInd_iff, SOccurs_mu by done; itauto |].
      by apply svar_sub_rename_not_occurs.
    + constructor; [done |].
      by inversion 1; subst; contradict Hocc; constructor.
Qed.

Definition esubst (phi : Pattern) (x : EVar) (psi : Pattern) :=
  let phi_psi_evars := EV phi ∪ EV psi : EVarSet in
  let phi_psi_svars := SV phi ∪ SV psi : SVarSet in
  let bound_phi_psi_evar_set := BEV phi ∩ EV psi : EVarSet in
  let bound_phi_psi_evars := elements bound_phi_psi_evar_set in
  let bound_phi_psi_svar_set := BSV phi ∩ SV psi  : SVarSet in
  let bound_phi_psi_svars := elements bound_phi_psi_svar_set in
  let fresh_evars := fresh_list (length bound_phi_psi_evars) phi_psi_evars in
  let fresh_svars := fresh_list (length bound_phi_psi_svars) phi_psi_svars in
  let etheta := evar_rename_iter bound_phi_psi_evars fresh_evars phi in
  let theta := svar_rename_iter bound_phi_psi_svars fresh_svars etheta in
  evar_sub0 x psi theta.

Definition ssubst (phi : Pattern) (x : SVar) (psi : Pattern) :=
  let phi_psi_evars := EV phi ∪ EV psi : EVarSet in
  let phi_psi_svars := SV phi ∪ SV psi : SVarSet in
  let bound_phi_psi_evar_set := BEV phi ∩ EV psi : EVarSet in
  let bound_phi_psi_evars := elements bound_phi_psi_evar_set in
  let bound_phi_psi_svar_set := BSV phi ∩ SV psi  : SVarSet in
  let bound_phi_psi_svars := elements bound_phi_psi_svar_set in
  let fresh_evars := fresh_list (length bound_phi_psi_evars) phi_psi_evars in
  let fresh_svars := fresh_list (length bound_phi_psi_svars) phi_psi_svars in
  let etheta := evar_rename_iter bound_phi_psi_evars fresh_evars phi in
  let theta := svar_rename_iter bound_phi_psi_svars fresh_svars etheta in
  svar_sub0 x psi theta.

Definition pNu (X : SVar) (phi : Pattern) :=
  pNeg (PMu X (pNeg (svar_sub0 X (pNeg (PSVar X)) phi))).

End sec_substitution.
