From stdpp Require Import prelude.


Section sec_elem_of_list_split_alt.

Context
  {A : Type}
  `{EqDecision A}
  (a : A).

Fixpoint drop_until_eq (l : list A) : list A :=
  match l with
  | [] => []
  | x :: l => if decide (x = a) then l else drop_until_eq l
  end.

Fixpoint take_while_not_eq (l : list A) : list A :=
  match l with
  | [] => []
  | x :: l => if decide (x = a) then [] else x :: take_while_not_eq l
  end.

Lemma elem_of_list_split_alt l :
  a ∈ l -> l = take_while_not_eq l ++ a :: drop_until_eq l.
Proof.
  induction l; [by inversion 1 |]; inversion 1; subst; cbn.
  - by rewrite !decide_True by done.
  - case_decide; [subst; done |].
    by cbn; f_equal; apply IHl.
Qed.

End sec_elem_of_list_split_alt.
