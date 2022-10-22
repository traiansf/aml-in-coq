From Cdcl Require Import Itauto. #[local] Tactic Notation "itauto" := itauto auto.
From stdpp Require Import prelude.
From AML Require Import Functions Ensemble.
From AML Require Import Signature Ensemble Structure.

Section sec_valuation.

Context
  `{s : Structure}.


Record Valuation : Type :=
{
  eval : EVar -> idomain;
  sval : SVar -> Ensemble idomain
}.

#[export] Instance ValudationInhabited : Inhabited Valuation :=
  populate {| eval := const inhabitant; sval := const ∅ |}.

Definition valuation_eupdate (e : Valuation) (x : EVar) (a : idomain) : Valuation :=
{|
  eval := fn_update (eval e) x a;
  sval := sval e
|}.

Lemma valuation_eupdate_id (e : Valuation) (x : EVar) :
  valuation_eupdate e x (eval e x) = e.
Proof.
  destruct e; unfold valuation_eupdate; cbn; f_equal; apply fn_update_id.
Qed.

Lemma valuation_eupdate_eq e x a : eval (valuation_eupdate e x a) x = a.
Proof. by destruct e; cbn; apply fn_update_eq. Qed.

Lemma valuation_eupdate_comm e x a y b :
  x <> y ->
  valuation_eupdate (valuation_eupdate e x a) y b
    =
  valuation_eupdate (valuation_eupdate e y b) x a.
Proof.
  intro Hxy; destruct e; unfold valuation_eupdate; cbn; f_equal.
  by apply fn_update_comm.
Qed.

Definition valuation_supdate (e : Valuation) (x : SVar) (a : Ensemble idomain) : Valuation :=
{|
  eval := eval e;
  sval := fn_update (sval e) x a
|}.

Lemma valuation_supdate_id (e : Valuation) (x : SVar) :
  valuation_supdate e x (sval e x) = e.
Proof.
  destruct e; unfold valuation_supdate; cbn; f_equal; apply fn_update_id.
Qed.

Lemma valuation_supdate_eq e x a : sval (valuation_supdate e x a) x = a.
Proof. by destruct e; cbn; apply fn_update_eq. Qed.

Lemma valuation_supdate_comm e x a y b :
  x <> y ->
  valuation_supdate (valuation_supdate e x a) y b
    =
  valuation_supdate (valuation_supdate e y b) x a.
Proof.
  intro Hxy; destruct e; unfold valuation_supdate; cbn; f_equal.
  by apply fn_update_comm.
Qed.

Lemma valuation_esupdate_comm e x a y b :
  valuation_supdate (valuation_eupdate e x a) y b
    =
  valuation_eupdate (valuation_supdate e y b) x a.
Proof. by destruct e. Qed.

End sec_valuation.
