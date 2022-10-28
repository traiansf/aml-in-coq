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

Definition evar_rename_iter (xs ys : list EVar) (p : Pattern) : Pattern :=
  foldr (fun (xy : EVar * EVar) (p : Pattern) => evar_rename xy.1 xy.2 p)
    p (zip xs ys).

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

Lemma evar_rename_not_bound x y phi :
  x <> y -> ~ EVarBound x (evar_rename x y phi).
Proof.
  intros; induction phi; cbn. 1-3, 5-7: by inversion 1.
  - case_decide; cbn.
    + inversion 1; [done | subst].
      by eapply evar_sub_rename_not_occurs, EOccursInd_iff; [| right].
    + by contradict IHphi; inversion IHphi.
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
  by inversion 1; intro; apply evar_rename_not_bound.
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

Definition svar_rename_iter (xs ys : list SVar) (p : Pattern) : Pattern :=
  foldr (fun (xy : SVar * SVar) (p : Pattern) => svar_rename xy.1 xy.2 p)
    p (zip xs ys).

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
