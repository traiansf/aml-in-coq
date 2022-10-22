From stdpp Require Import prelude.
From AML Require Import Signature Pattern Variables Substitution.


Class BotClosed {sign : signature} (P : @Pattern sign -> Prop) :=
{
  bot_closed : P (@PBot sign)
}.

Class TopClosed {sign : signature} (P : @Pattern sign -> Prop) :=
{
  top_closed : P (@pTop sign)
}.

Class NegClosed {sign : signature} (P : @Pattern sign -> Prop) :=
{
  neg_closed : forall phi, P phi -> P (pNeg phi)
}.

Class ImplClosed {sign : signature} (P : @Pattern sign -> Prop) :=
{
  impl_closed : forall phi psi, P phi -> P psi -> P (PImpl phi psi)
}.

Class AndClosed {sign : signature} (P : @Pattern sign -> Prop) :=
{
  and_closed : forall phi psi, P phi -> P psi -> P (pAnd phi psi)
}.

Class OrClosed {sign : signature} (P : @Pattern sign -> Prop) :=
{
  or_closed : forall phi psi, P phi -> P psi -> P (pOr phi psi)
}.

Class IffClosed {sign : signature} (P : @Pattern sign -> Prop) :=
{
  iff_closed : forall phi psi, P phi -> P psi -> P (pIff phi psi)
}.

Class FiniteConjunctionClosed {sign : signature} (P : @Pattern sign -> Prop) :=
{
  finite_conjunction_closed :
    forall phis, Forall P phis -> P (finite_conjunction phis)
}.

Class FiniteDisjunctionClosed {sign : signature} (P : @Pattern sign -> Prop) :=
{
  finite_disjunction_closed :
    forall phis, Forall P phis -> P (finite_disjunction phis)
}.

Class ExClosed {sign : signature} (P : @Pattern sign -> Prop) :=
{
  ex_closed : forall x phi, P phi -> P (PEx x phi)
}.

Class AllClosed {sign : signature} (P : @Pattern sign -> Prop) :=
{
  all_closed : forall x phi, P phi -> P (pAll x phi)
}.

Class MuClosed {sign : signature} (P : @Pattern sign -> Prop) :=
{
  mu_closed : forall X phi, OccursPositively X phi -> P phi -> P (PMu X phi)
}.

Class NuClosed {sign : signature} (P : @Pattern sign -> Prop) :=
{
  nu_closed : forall X phi, OccursPositively X phi -> P phi -> P (pNu X phi)
}.

Section sec_pattern_closure_properties.

Context
  `{BotClosed P}
  `{!ImplClosed P}.

#[export] Instance closed_neg : NegClosed P.
Proof. by constructor; intros phi Hphi; apply impl_closed; [| apply bot_closed]. Qed.

#[export] Instance closed_top : TopClosed P.
Proof. by constructor; apply neg_closed, bot_closed. Qed.

#[export] Instance closed_or : OrClosed P.
Proof. by constructor; intros phi psi Hphi Hpsi; apply impl_closed; [apply neg_closed |]. Qed.

#[export] Instance closed_and : AndClosed P.
Proof.
  by constructor; intros phi psi Hphi Hpsi; apply neg_closed, or_closed; apply neg_closed.
Qed.

#[export] Instance closed_iff : IffClosed P.
Proof. by constructor; intros phi psi Hphi Hpsi; apply and_closed; apply impl_closed. Qed.

#[export] Instance closed_finite_conjunction : FiniteConjunctionClosed P.
Proof.
  by constructor; intros phis; induction 1;
    [apply top_closed | apply and_closed].
Qed.

#[export] Instance closed_finite_disjunction : FiniteDisjunctionClosed P.
Proof.
  by constructor; intros phis; induction 1;
    [apply bot_closed | apply or_closed].
Qed.

#[export] Instance closed_all `{!ExClosed P} : AllClosed P.
Proof. by constructor; intros x phi Hphi; apply neg_closed, ex_closed, neg_closed. Qed.

End sec_pattern_closure_properties.

Section sec_closed_pattern_closure_properties.

Context [sign : signature].

#[export] Instance closed_pattern_bot : BotClosed (@ClosedPattern sign).
Proof. by constructor; constructor; inversion 1. Qed.

#[export] Instance closed_pattern_impl : ImplClosed (@ClosedPattern sign).
Proof.
  by constructor; intros phi psi [] []; constructor; inversion 1; subst; firstorder.
Qed.

#[export] Instance closed_pattern_ex : ExClosed (@ClosedPattern sign).
Proof.
  by constructor; intros x phi []; constructor; inversion 1; subst; firstorder.
Qed.

#[export] Instance closed_pattern_mu : MuClosed (@ClosedPattern sign).
Proof.
  by constructor; intros x phi Hpos []; constructor; inversion 1; subst; firstorder.
Qed.

End sec_closed_pattern_closure_properties.
