Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export Fsub_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme typ_ind' := Induction for typ Sort Prop.

Definition typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  typ_ind' H1 H2 H3 H4 H5 H6 H7.

Scheme typ_rec' := Induction for typ Sort Set.

Definition typ_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  typ_rec' H1 H2 H3 H4 H5 H6 H7.

Scheme binding_ind' := Induction for binding Sort Prop.

Definition binding_mutind :=
  fun H1 H2 H3 =>
  binding_ind' H1 H2 H3.

Scheme binding_rec' := Induction for binding Sort Set.

Definition binding_mutrec :=
  fun H1 H2 H3 =>
  binding_rec' H1 H2 H3.

Scheme exp_ind' := Induction for exp Sort Prop.

Definition exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Scheme exp_rec' := Induction for exp Sort Set.

Definition exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_typ_wrt_typ_rec (n1 : nat) (X1 : typvar) (T1 : typ) {struct T1} : typ :=
  match T1 with
    | typ_top => typ_top
    | typ_var_f X2 => if (X1 == X2) then (typ_var_b n1) else (typ_var_f X2)
    | typ_var_b n2 => if (lt_ge_dec n2 n1) then (typ_var_b n2) else (typ_var_b (S n2))
    | typ_arrow T2 T3 => typ_arrow (close_typ_wrt_typ_rec n1 X1 T2) (close_typ_wrt_typ_rec n1 X1 T3)
    | typ_all T2 T3 => typ_all (close_typ_wrt_typ_rec n1 X1 T2) (close_typ_wrt_typ_rec (S n1) X1 T3)
    | typ_sum T2 T3 => typ_sum (close_typ_wrt_typ_rec n1 X1 T2) (close_typ_wrt_typ_rec n1 X1 T3)
  end.

Definition close_typ_wrt_typ X1 T1 := close_typ_wrt_typ_rec 0 X1 T1.

Fixpoint close_binding_wrt_typ_rec (n1 : nat) (X1 : typvar) (b1 : binding) {struct b1} : binding :=
  match b1 with
    | bind_sub T1 => bind_sub (close_typ_wrt_typ_rec n1 X1 T1)
    | bind_typ T1 => bind_typ (close_typ_wrt_typ_rec n1 X1 T1)
  end.

Definition close_binding_wrt_typ X1 b1 := close_binding_wrt_typ_rec 0 X1 b1.

Fixpoint close_exp_wrt_typ_rec (n1 : nat) (X1 : typvar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | exp_var_f x1 => exp_var_f x1
    | exp_var_b n2 => exp_var_b n2
    | exp_abs T1 e2 => exp_abs (close_typ_wrt_typ_rec n1 X1 T1) (close_exp_wrt_typ_rec n1 X1 e2)
    | exp_app e2 e3 => exp_app (close_exp_wrt_typ_rec n1 X1 e2) (close_exp_wrt_typ_rec n1 X1 e3)
    | exp_tabs T1 e2 => exp_tabs (close_typ_wrt_typ_rec n1 X1 T1) (close_exp_wrt_typ_rec (S n1) X1 e2)
    | exp_tapp e2 T1 => exp_tapp (close_exp_wrt_typ_rec n1 X1 e2) (close_typ_wrt_typ_rec n1 X1 T1)
    | exp_let e2 e3 => exp_let (close_exp_wrt_typ_rec n1 X1 e2) (close_exp_wrt_typ_rec n1 X1 e3)
    | exp_inl e2 => exp_inl (close_exp_wrt_typ_rec n1 X1 e2)
    | exp_inr e2 => exp_inr (close_exp_wrt_typ_rec n1 X1 e2)
    | exp_case e2 e3 e4 => exp_case (close_exp_wrt_typ_rec n1 X1 e2) (close_exp_wrt_typ_rec n1 X1 e3) (close_exp_wrt_typ_rec n1 X1 e4)
  end.

Fixpoint close_exp_wrt_exp_rec (n1 : nat) (x1 : expvar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | exp_var_f x2 => if (x1 == x2) then (exp_var_b n1) else (exp_var_f x2)
    | exp_var_b n2 => if (lt_ge_dec n2 n1) then (exp_var_b n2) else (exp_var_b (S n2))
    | exp_abs T1 e2 => exp_abs T1 (close_exp_wrt_exp_rec (S n1) x1 e2)
    | exp_app e2 e3 => exp_app (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | exp_tabs T1 e2 => exp_tabs T1 (close_exp_wrt_exp_rec n1 x1 e2)
    | exp_tapp e2 T1 => exp_tapp (close_exp_wrt_exp_rec n1 x1 e2) T1
    | exp_let e2 e3 => exp_let (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec (S n1) x1 e3)
    | exp_inl e2 => exp_inl (close_exp_wrt_exp_rec n1 x1 e2)
    | exp_inr e2 => exp_inr (close_exp_wrt_exp_rec n1 x1 e2)
    | exp_case e2 e3 e4 => exp_case (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec (S n1) x1 e3) (close_exp_wrt_exp_rec (S n1) x1 e4)
  end.

Definition close_exp_wrt_typ X1 e1 := close_exp_wrt_typ_rec 0 X1 e1.

Definition close_exp_wrt_exp x1 e1 := close_exp_wrt_exp_rec 0 x1 e1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_typ (T1 : typ) {struct T1} : nat :=
  match T1 with
    | typ_top => 1
    | typ_var_f X1 => 1
    | typ_var_b n1 => 1
    | typ_arrow T2 T3 => 1 + (size_typ T2) + (size_typ T3)
    | typ_all T2 T3 => 1 + (size_typ T2) + (size_typ T3)
    | typ_sum T2 T3 => 1 + (size_typ T2) + (size_typ T3)
  end.

Fixpoint size_binding (b1 : binding) {struct b1} : nat :=
  match b1 with
    | bind_sub T1 => 1 + (size_typ T1)
    | bind_typ T1 => 1 + (size_typ T1)
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | exp_var_f x1 => 1
    | exp_var_b n1 => 1
    | exp_abs T1 e2 => 1 + (size_typ T1) + (size_exp e2)
    | exp_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_tabs T1 e2 => 1 + (size_typ T1) + (size_exp e2)
    | exp_tapp e2 T1 => 1 + (size_exp e2) + (size_typ T1)
    | exp_let e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_inl e2 => 1 + (size_exp e2)
    | exp_inr e2 => 1 + (size_exp e2)
    | exp_case e2 e3 e4 => 1 + (size_exp e2) + (size_exp e3) + (size_exp e4)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_typ_wrt_typ : nat -> typ -> Prop :=
  | degree_wrt_typ_typ_top : forall n1,
    degree_typ_wrt_typ n1 (typ_top)
  | degree_wrt_typ_typ_var_f : forall n1 X1,
    degree_typ_wrt_typ n1 (typ_var_f X1)
  | degree_wrt_typ_typ_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_typ_wrt_typ n1 (typ_var_b n2)
  | degree_wrt_typ_typ_arrow : forall n1 T1 T2,
    degree_typ_wrt_typ n1 T1 ->
    degree_typ_wrt_typ n1 T2 ->
    degree_typ_wrt_typ n1 (typ_arrow T1 T2)
  | degree_wrt_typ_typ_all : forall n1 T1 T2,
    degree_typ_wrt_typ n1 T1 ->
    degree_typ_wrt_typ (S n1) T2 ->
    degree_typ_wrt_typ n1 (typ_all T1 T2)
  | degree_wrt_typ_typ_sum : forall n1 T1 T2,
    degree_typ_wrt_typ n1 T1 ->
    degree_typ_wrt_typ n1 T2 ->
    degree_typ_wrt_typ n1 (typ_sum T1 T2).

Scheme degree_typ_wrt_typ_ind' := Induction for degree_typ_wrt_typ Sort Prop.

Definition degree_typ_wrt_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  degree_typ_wrt_typ_ind' H1 H2 H3 H4 H5 H6 H7.

Hint Constructors degree_typ_wrt_typ : core lngen.

Inductive degree_binding_wrt_typ : nat -> binding -> Prop :=
  | degree_wrt_typ_bind_sub : forall n1 T1,
    degree_typ_wrt_typ n1 T1 ->
    degree_binding_wrt_typ n1 (bind_sub T1)
  | degree_wrt_typ_bind_typ : forall n1 T1,
    degree_typ_wrt_typ n1 T1 ->
    degree_binding_wrt_typ n1 (bind_typ T1).

Scheme degree_binding_wrt_typ_ind' := Induction for degree_binding_wrt_typ Sort Prop.

Definition degree_binding_wrt_typ_mutind :=
  fun H1 H2 H3 =>
  degree_binding_wrt_typ_ind' H1 H2 H3.

Hint Constructors degree_binding_wrt_typ : core lngen.

Inductive degree_exp_wrt_typ : nat -> exp -> Prop :=
  | degree_wrt_typ_exp_var_f : forall n1 x1,
    degree_exp_wrt_typ n1 (exp_var_f x1)
  | degree_wrt_typ_exp_var_b : forall n1 n2,
    degree_exp_wrt_typ n1 (exp_var_b n2)
  | degree_wrt_typ_exp_abs : forall n1 T1 e1,
    degree_typ_wrt_typ n1 T1 ->
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (exp_abs T1 e1)
  | degree_wrt_typ_exp_app : forall n1 e1 e2,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 e2 ->
    degree_exp_wrt_typ n1 (exp_app e1 e2)
  | degree_wrt_typ_exp_tabs : forall n1 T1 e1,
    degree_typ_wrt_typ n1 T1 ->
    degree_exp_wrt_typ (S n1) e1 ->
    degree_exp_wrt_typ n1 (exp_tabs T1 e1)
  | degree_wrt_typ_exp_tapp : forall n1 e1 T1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 T1 ->
    degree_exp_wrt_typ n1 (exp_tapp e1 T1)
  | degree_wrt_typ_exp_let : forall n1 e1 e2,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 e2 ->
    degree_exp_wrt_typ n1 (exp_let e1 e2)
  | degree_wrt_typ_exp_inl : forall n1 e1,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (exp_inl e1)
  | degree_wrt_typ_exp_inr : forall n1 e1,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (exp_inr e1)
  | degree_wrt_typ_exp_case : forall n1 e1 e2 e3,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 e2 ->
    degree_exp_wrt_typ n1 e3 ->
    degree_exp_wrt_typ n1 (exp_case e1 e2 e3).

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
  | degree_wrt_exp_exp_var_f : forall n1 x1,
    degree_exp_wrt_exp n1 (exp_var_f x1)
  | degree_wrt_exp_exp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_exp_wrt_exp n1 (exp_var_b n2)
  | degree_wrt_exp_exp_abs : forall n1 T1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (exp_abs T1 e1)
  | degree_wrt_exp_exp_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (exp_app e1 e2)
  | degree_wrt_exp_exp_tabs : forall n1 T1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_tabs T1 e1)
  | degree_wrt_exp_exp_tapp : forall n1 e1 T1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_tapp e1 T1)
  | degree_wrt_exp_exp_let : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp (S n1) e2 ->
    degree_exp_wrt_exp n1 (exp_let e1 e2)
  | degree_wrt_exp_exp_inl : forall n1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_inl e1)
  | degree_wrt_exp_exp_inr : forall n1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_inr e1)
  | degree_wrt_exp_exp_case : forall n1 e1 e2 e3,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp (S n1) e2 ->
    degree_exp_wrt_exp (S n1) e3 ->
    degree_exp_wrt_exp n1 (exp_case e1 e2 e3).

Scheme degree_exp_wrt_typ_ind' := Induction for degree_exp_wrt_typ Sort Prop.

Definition degree_exp_wrt_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  degree_exp_wrt_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Definition degree_exp_wrt_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  degree_exp_wrt_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Hint Constructors degree_exp_wrt_typ : core lngen.

Hint Constructors degree_exp_wrt_exp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_typ : typ -> Set :=
  | lc_set_typ_top :
    lc_set_typ (typ_top)
  | lc_set_typ_var_f : forall X1,
    lc_set_typ (typ_var_f X1)
  | lc_set_typ_arrow : forall T1 T2,
    lc_set_typ T1 ->
    lc_set_typ T2 ->
    lc_set_typ (typ_arrow T1 T2)
  | lc_set_typ_all : forall T1 T2,
    lc_set_typ T1 ->
    (forall X1 : typvar, lc_set_typ (open_typ_wrt_typ T2 (typ_var_f X1))) ->
    lc_set_typ (typ_all T1 T2)
  | lc_set_typ_sum : forall T1 T2,
    lc_set_typ T1 ->
    lc_set_typ T2 ->
    lc_set_typ (typ_sum T1 T2).

Scheme lc_typ_ind' := Induction for lc_typ Sort Prop.

Definition lc_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 =>
  lc_typ_ind' H1 H2 H3 H4 H5 H6.

Scheme lc_set_typ_ind' := Induction for lc_set_typ Sort Prop.

Definition lc_set_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 =>
  lc_set_typ_ind' H1 H2 H3 H4 H5 H6.

Scheme lc_set_typ_rec' := Induction for lc_set_typ Sort Set.

Definition lc_set_typ_mutrec :=
  fun H1 H2 H3 H4 H5 H6 =>
  lc_set_typ_rec' H1 H2 H3 H4 H5 H6.

Hint Constructors lc_typ : core lngen.

Hint Constructors lc_set_typ : core lngen.

Inductive lc_set_binding : binding -> Set :=
  | lc_set_bind_sub : forall T1,
    lc_set_typ T1 ->
    lc_set_binding (bind_sub T1)
  | lc_set_bind_typ : forall T1,
    lc_set_typ T1 ->
    lc_set_binding (bind_typ T1).

Scheme lc_binding_ind' := Induction for lc_binding Sort Prop.

Definition lc_binding_mutind :=
  fun H1 H2 H3 =>
  lc_binding_ind' H1 H2 H3.

Scheme lc_set_binding_ind' := Induction for lc_set_binding Sort Prop.

Definition lc_set_binding_mutind :=
  fun H1 H2 H3 =>
  lc_set_binding_ind' H1 H2 H3.

Scheme lc_set_binding_rec' := Induction for lc_set_binding Sort Set.

Definition lc_set_binding_mutrec :=
  fun H1 H2 H3 =>
  lc_set_binding_rec' H1 H2 H3.

Hint Constructors lc_binding : core lngen.

Hint Constructors lc_set_binding : core lngen.

Inductive lc_set_exp : exp -> Set :=
  | lc_set_exp_var_f : forall x1,
    lc_set_exp (exp_var_f x1)
  | lc_set_exp_abs : forall T1 e1,
    lc_set_typ T1 ->
    (forall x1 : expvar, lc_set_exp (open_exp_wrt_exp e1 (exp_var_f x1))) ->
    lc_set_exp (exp_abs T1 e1)
  | lc_set_exp_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (exp_app e1 e2)
  | lc_set_exp_tabs : forall T1 e1,
    lc_set_typ T1 ->
    (forall X1 : typvar, lc_set_exp (open_exp_wrt_typ e1 (typ_var_f X1))) ->
    lc_set_exp (exp_tabs T1 e1)
  | lc_set_exp_tapp : forall e1 T1,
    lc_set_exp e1 ->
    lc_set_typ T1 ->
    lc_set_exp (exp_tapp e1 T1)
  | lc_set_exp_let : forall e1 e2,
    lc_set_exp e1 ->
    (forall x1 : expvar, lc_set_exp (open_exp_wrt_exp e2 (exp_var_f x1))) ->
    lc_set_exp (exp_let e1 e2)
  | lc_set_exp_inl : forall e1,
    lc_set_exp e1 ->
    lc_set_exp (exp_inl e1)
  | lc_set_exp_inr : forall e1,
    lc_set_exp e1 ->
    lc_set_exp (exp_inr e1)
  | lc_set_exp_case : forall e1 e2 e3,
    lc_set_exp e1 ->
    (forall x1 : expvar, lc_set_exp (open_exp_wrt_exp e2 (exp_var_f x1))) ->
    (forall y1 : expvar, lc_set_exp (open_exp_wrt_exp e3 (exp_var_f y1))) ->
    lc_set_exp (exp_case e1 e2 e3).

Scheme lc_exp_ind' := Induction for lc_exp Sort Prop.

Definition lc_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  lc_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme lc_set_exp_ind' := Induction for lc_set_exp Sort Prop.

Definition lc_set_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  lc_set_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme lc_set_exp_rec' := Induction for lc_set_exp Sort Set.

Definition lc_set_exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  lc_set_exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Hint Constructors lc_exp : core lngen.

Hint Constructors lc_set_exp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_typ_wrt_typ T1 := forall X1, lc_typ (open_typ_wrt_typ T1 (typ_var_f X1)).

Hint Unfold body_typ_wrt_typ : core.

Definition body_binding_wrt_typ b1 := forall X1, lc_binding (open_binding_wrt_typ b1 (typ_var_f X1)).

Hint Unfold body_binding_wrt_typ : core.

Definition body_exp_wrt_typ e1 := forall X1, lc_exp (open_exp_wrt_typ e1 (typ_var_f X1)).

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)).

Hint Unfold body_exp_wrt_typ : core.

Hint Unfold body_exp_wrt_exp : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_typ_min_mutual :
(forall T1, 1 <= size_typ T1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_typ_min :
forall T1, 1 <= size_typ T1.
Proof.
pose proof size_typ_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_min : lngen.

(* begin hide *)

Lemma size_binding_min_mutual :
(forall b1, 1 <= size_binding b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_binding_min :
forall b1, 1 <= size_binding b1.
Proof.
pose proof size_binding_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_binding_min : lngen.

(* begin hide *)

Lemma size_exp_min_mutual :
(forall e1, 1 <= size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_exp_min :
forall e1, 1 <= size_exp e1.
Proof.
pose proof size_exp_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_min : lngen.

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec_mutual :
(forall T1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 T1) = size_typ T1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec :
forall T1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 T1) = size_typ T1.
Proof.
pose proof size_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_close_typ_wrt_typ_rec : lngen.
Hint Rewrite size_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_binding_close_binding_wrt_typ_rec_mutual :
(forall b1 X1 n1,
  size_binding (close_binding_wrt_typ_rec n1 X1 b1) = size_binding b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_binding_close_binding_wrt_typ_rec :
forall b1 X1 n1,
  size_binding (close_binding_wrt_typ_rec n1 X1 b1) = size_binding b1.
Proof.
pose proof size_binding_close_binding_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_binding_close_binding_wrt_typ_rec : lngen.
Hint Rewrite size_binding_close_binding_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  size_exp (close_exp_wrt_typ_rec n1 X1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  size_exp (close_exp_wrt_typ_rec n1 X1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_close_exp_wrt_typ_rec : lngen.
Hint Rewrite size_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite size_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_close_typ_wrt_typ :
forall T1 X1,
  size_typ (close_typ_wrt_typ X1 T1) = size_typ T1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve size_typ_close_typ_wrt_typ : lngen.
Hint Rewrite size_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma size_binding_close_binding_wrt_typ :
forall b1 X1,
  size_binding (close_binding_wrt_typ X1 b1) = size_binding b1.
Proof.
unfold close_binding_wrt_typ; default_simp.
Qed.

Hint Resolve size_binding_close_binding_wrt_typ : lngen.
Hint Rewrite size_binding_close_binding_wrt_typ using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_typ :
forall e1 X1,
  size_exp (close_exp_wrt_typ X1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve size_exp_close_exp_wrt_typ : lngen.
Hint Rewrite size_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_exp :
forall e1 x1,
  size_exp (close_exp_wrt_exp x1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve size_exp_close_exp_wrt_exp : lngen.
Hint Rewrite size_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_mutual :
(forall T1 T2 n1,
  size_typ T1 <= size_typ (open_typ_wrt_typ_rec n1 T2 T1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec :
forall T1 T2 n1,
  size_typ T1 <= size_typ (open_typ_wrt_typ_rec n1 T2 T1).
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_binding_open_binding_wrt_typ_rec_mutual :
(forall b1 T1 n1,
  size_binding b1 <= size_binding (open_binding_wrt_typ_rec n1 T1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_binding_open_binding_wrt_typ_rec :
forall b1 T1 n1,
  size_binding b1 <= size_binding (open_binding_wrt_typ_rec n1 T1 b1).
Proof.
pose proof size_binding_open_binding_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_binding_open_binding_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 T1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_typ_rec n1 T1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec :
forall e1 T1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_typ_rec n1 T1 e1).
Proof.
pose proof size_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ :
forall T1 T2,
  size_typ T1 <= size_typ (open_typ_wrt_typ T1 T2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ : lngen.

Lemma size_binding_open_binding_wrt_typ :
forall b1 T1,
  size_binding b1 <= size_binding (open_binding_wrt_typ b1 T1).
Proof.
unfold open_binding_wrt_typ; default_simp.
Qed.

Hint Resolve size_binding_open_binding_wrt_typ : lngen.

Lemma size_exp_open_exp_wrt_typ :
forall e1 T1,
  size_exp e1 <= size_exp (open_exp_wrt_typ e1 T1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_typ : lngen.

Lemma size_exp_open_exp_wrt_exp :
forall e1 e2,
  size_exp e1 <= size_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var_mutual :
(forall T1 X1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (typ_var_f X1) T1) = size_typ T1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var :
forall T1 X1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (typ_var_f X1) T1) = size_typ T1.
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ_rec_var : lngen.
Hint Rewrite size_typ_open_typ_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_binding_open_binding_wrt_typ_rec_var_mutual :
(forall b1 X1 n1,
  size_binding (open_binding_wrt_typ_rec n1 (typ_var_f X1) b1) = size_binding b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_binding_open_binding_wrt_typ_rec_var :
forall b1 X1 n1,
  size_binding (open_binding_wrt_typ_rec n1 (typ_var_f X1) b1) = size_binding b1.
Proof.
pose proof size_binding_open_binding_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_binding_open_binding_wrt_typ_rec_var : lngen.
Hint Rewrite size_binding_open_binding_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_var_mutual :
(forall e1 X1 n1,
  size_exp (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_var :
forall e1 X1 n1,
  size_exp (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_typ_rec_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var_mutual :
(forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var :
forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_rec_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ_var :
forall T1 X1,
  size_typ (open_typ_wrt_typ T1 (typ_var_f X1)) = size_typ T1.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ_var : lngen.
Hint Rewrite size_typ_open_typ_wrt_typ_var using solve [auto] : lngen.

Lemma size_binding_open_binding_wrt_typ_var :
forall b1 X1,
  size_binding (open_binding_wrt_typ b1 (typ_var_f X1)) = size_binding b1.
Proof.
unfold open_binding_wrt_typ; default_simp.
Qed.

Hint Resolve size_binding_open_binding_wrt_typ_var : lngen.
Hint Rewrite size_binding_open_binding_wrt_typ_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_typ_var :
forall e1 X1,
  size_exp (open_exp_wrt_typ e1 (typ_var_f X1)) = size_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_typ_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_typ_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_exp_var :
forall e1 x1,
  size_exp (open_exp_wrt_exp e1 (exp_var_f x1)) = size_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_exp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_typ_wrt_typ_S_mutual :
(forall n1 T1,
  degree_typ_wrt_typ n1 T1 ->
  degree_typ_wrt_typ (S n1) T1).
Proof.
apply_mutual_ind degree_typ_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_S :
forall n1 T1,
  degree_typ_wrt_typ n1 T1 ->
  degree_typ_wrt_typ (S n1) T1.
Proof.
pose proof degree_typ_wrt_typ_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_binding_wrt_typ_S_mutual :
(forall n1 b1,
  degree_binding_wrt_typ n1 b1 ->
  degree_binding_wrt_typ (S n1) b1).
Proof.
apply_mutual_ind degree_binding_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_binding_wrt_typ_S :
forall n1 b1,
  degree_binding_wrt_typ n1 b1 ->
  degree_binding_wrt_typ (S n1) b1.
Proof.
pose proof degree_binding_wrt_typ_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_binding_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_typ_S_mutual :
(forall n1 e1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_typ_S :
forall n1 e1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) e1.
Proof.
pose proof degree_exp_wrt_typ_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_S_mutual :
(forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_S :
forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_S : lngen.

Lemma degree_typ_wrt_typ_O :
forall n1 T1,
  degree_typ_wrt_typ O T1 ->
  degree_typ_wrt_typ n1 T1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_typ_wrt_typ_O : lngen.

Lemma degree_binding_wrt_typ_O :
forall n1 b1,
  degree_binding_wrt_typ O b1 ->
  degree_binding_wrt_typ n1 b1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_binding_wrt_typ_O : lngen.

Lemma degree_exp_wrt_typ_O :
forall n1 e1,
  degree_exp_wrt_typ O e1 ->
  degree_exp_wrt_typ n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_exp_wrt_typ_O : lngen.

Lemma degree_exp_wrt_exp_O :
forall n1 e1,
  degree_exp_wrt_exp O e1 ->
  degree_exp_wrt_exp n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_O : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual :
(forall T1 X1 n1,
  degree_typ_wrt_typ n1 T1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 T1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec :
forall T1 X1 n1,
  degree_typ_wrt_typ n1 T1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 T1).
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_typ_close_binding_wrt_typ_rec_mutual :
(forall b1 X1 n1,
  degree_binding_wrt_typ n1 b1 ->
  degree_binding_wrt_typ (S n1) (close_binding_wrt_typ_rec n1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_typ_close_binding_wrt_typ_rec :
forall b1 X1 n1,
  degree_binding_wrt_typ n1 b1 ->
  degree_binding_wrt_typ (S n1) (close_binding_wrt_typ_rec n1 X1 b1).
Proof.
pose proof degree_binding_wrt_typ_close_binding_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_binding_wrt_typ_close_binding_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_close_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec :
forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_close_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ :
forall T1 X1,
  degree_typ_wrt_typ 0 T1 ->
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 T1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ : lngen.

Lemma degree_binding_wrt_typ_close_binding_wrt_typ :
forall b1 X1,
  degree_binding_wrt_typ 0 b1 ->
  degree_binding_wrt_typ 1 (close_binding_wrt_typ X1 b1).
Proof.
unfold close_binding_wrt_typ; default_simp.
Qed.

Hint Resolve degree_binding_wrt_typ_close_binding_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_typ :
forall e1 X1,
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_typ 1 (close_exp_wrt_typ X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve degree_exp_wrt_typ_close_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_typ_close_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (close_exp_wrt_typ X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  degree_exp_wrt_exp 0 e1 ->
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual :
(forall T1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 T1) ->
  degree_typ_wrt_typ n1 T1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv :
forall T1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 T1) ->
  degree_typ_wrt_typ n1 T1.
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_typ_close_binding_wrt_typ_rec_inv_mutual :
(forall b1 X1 n1,
  degree_binding_wrt_typ (S n1) (close_binding_wrt_typ_rec n1 X1 b1) ->
  degree_binding_wrt_typ n1 b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_typ_close_binding_wrt_typ_rec_inv :
forall b1 X1 n1,
  degree_binding_wrt_typ (S n1) (close_binding_wrt_typ_rec n1 X1 b1) ->
  degree_binding_wrt_typ n1 b1.
Proof.
pose proof degree_binding_wrt_typ_close_binding_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_binding_wrt_typ_close_binding_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1,
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_typ n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_typ n2 e1.
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_inv :
forall T1 X1,
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 T1) ->
  degree_typ_wrt_typ 0 T1.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_inv : lngen.

Lemma degree_binding_wrt_typ_close_binding_wrt_typ_inv :
forall b1 X1,
  degree_binding_wrt_typ 1 (close_binding_wrt_typ X1 b1) ->
  degree_binding_wrt_typ 0 b1.
Proof.
unfold close_binding_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_binding_wrt_typ_close_binding_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_inv :
forall e1 X1,
  degree_exp_wrt_typ 1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_typ 0 e1.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_typ_close_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_inv :
forall e1 x1 n1,
  degree_exp_wrt_typ n1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_typ_close_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_inv :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_inv :
forall e1 x1,
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_exp 0 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_inv : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual :
(forall T1 T2 n1,
  degree_typ_wrt_typ (S n1) T1 ->
  degree_typ_wrt_typ n1 T2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 T2 T1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec :
forall T1 T2 n1,
  degree_typ_wrt_typ (S n1) T1 ->
  degree_typ_wrt_typ n1 T2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 T2 T1).
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_typ_open_binding_wrt_typ_rec_mutual :
(forall b1 T1 n1,
  degree_binding_wrt_typ (S n1) b1 ->
  degree_typ_wrt_typ n1 T1 ->
  degree_binding_wrt_typ n1 (open_binding_wrt_typ_rec n1 T1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_typ_open_binding_wrt_typ_rec :
forall b1 T1 n1,
  degree_binding_wrt_typ (S n1) b1 ->
  degree_typ_wrt_typ n1 T1 ->
  degree_binding_wrt_typ n1 (open_binding_wrt_typ_rec n1 T1 b1).
Proof.
pose proof degree_binding_wrt_typ_open_binding_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_binding_wrt_typ_open_binding_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_mutual :
(forall e1 T1 n1,
  degree_exp_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 T1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 T1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec :
forall e1 T1 n1,
  degree_exp_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 T1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 T1 e1).
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec :
forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1).
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 T1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 T1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec :
forall e1 T1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 T1 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ :
forall T1 T2,
  degree_typ_wrt_typ 1 T1 ->
  degree_typ_wrt_typ 0 T2 ->
  degree_typ_wrt_typ 0 (open_typ_wrt_typ T1 T2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma degree_binding_wrt_typ_open_binding_wrt_typ :
forall b1 T1,
  degree_binding_wrt_typ 1 b1 ->
  degree_typ_wrt_typ 0 T1 ->
  degree_binding_wrt_typ 0 (open_binding_wrt_typ b1 T1).
Proof.
unfold open_binding_wrt_typ; default_simp.
Qed.

Hint Resolve degree_binding_wrt_typ_open_binding_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_typ :
forall e1 T1,
  degree_exp_wrt_typ 1 e1 ->
  degree_typ_wrt_typ 0 T1 ->
  degree_exp_wrt_typ 0 (open_exp_wrt_typ e1 T1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve degree_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_exp :
forall e1 e2 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_typ_open_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_typ :
forall e1 T1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ e1 T1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_open_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp :
forall e1 e2,
  degree_exp_wrt_exp 1 e1 ->
  degree_exp_wrt_exp 0 e2 ->
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual :
(forall T1 T2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 T2 T1) ->
  degree_typ_wrt_typ (S n1) T1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv :
forall T1 T2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 T2 T1) ->
  degree_typ_wrt_typ (S n1) T1.
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_typ_open_binding_wrt_typ_rec_inv_mutual :
(forall b1 T1 n1,
  degree_binding_wrt_typ n1 (open_binding_wrt_typ_rec n1 T1 b1) ->
  degree_binding_wrt_typ (S n1) b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_typ_open_binding_wrt_typ_rec_inv :
forall b1 T1 n1,
  degree_binding_wrt_typ n1 (open_binding_wrt_typ_rec n1 T1 b1) ->
  degree_binding_wrt_typ (S n1) b1.
Proof.
pose proof degree_binding_wrt_typ_open_binding_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_binding_wrt_typ_open_binding_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv_mutual :
(forall e1 T1 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 T1 e1) ->
  degree_exp_wrt_typ (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv :
forall e1 T1 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 T1 e1) ->
  degree_exp_wrt_typ (S n1) e1.
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv_mutual :
(forall e1 T1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 T1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv :
forall e1 T1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 T1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_inv :
forall T1 T2,
  degree_typ_wrt_typ 0 (open_typ_wrt_typ T1 T2) ->
  degree_typ_wrt_typ 1 T1.
Proof.
unfold open_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_inv : lngen.

Lemma degree_binding_wrt_typ_open_binding_wrt_typ_inv :
forall b1 T1,
  degree_binding_wrt_typ 0 (open_binding_wrt_typ b1 T1) ->
  degree_binding_wrt_typ 1 b1.
Proof.
unfold open_binding_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_binding_wrt_typ_open_binding_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_inv :
forall e1 T1,
  degree_exp_wrt_typ 0 (open_exp_wrt_typ e1 T1) ->
  degree_exp_wrt_typ 1 e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_typ_open_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_inv :
forall e1 e2 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_typ n1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_typ_open_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_inv :
forall e1 T1 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ e1 T1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_inv :
forall e1 e2,
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_exp 1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj_mutual :
(forall T1 T2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 T1 = close_typ_wrt_typ_rec n1 X1 T2 ->
  T1 = T2).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj :
forall T1 T2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 T1 = close_typ_wrt_typ_rec n1 X1 T2 ->
  T1 = T2.
Proof.
pose proof close_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_typ_rec_inj_mutual :
(forall b1 b2 X1 n1,
  close_binding_wrt_typ_rec n1 X1 b1 = close_binding_wrt_typ_rec n1 X1 b2 ->
  b1 = b2).
Proof.
apply_mutual_ind binding_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_typ_rec_inj :
forall b1 b2 X1 n1,
  close_binding_wrt_typ_rec n1 X1 b1 = close_binding_wrt_typ_rec n1 X1 b2 ->
  b1 = b2.
Proof.
pose proof close_binding_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_binding_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_inj_mutual :
(forall e1 e2 X1 n1,
  close_exp_wrt_typ_rec n1 X1 e1 = close_exp_wrt_typ_rec n1 X1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_inj :
forall e1 e2 X1 n1,
  close_exp_wrt_typ_rec n1 X1 e1 = close_exp_wrt_typ_rec n1 X1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_exp_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj :
forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_inj :
forall T1 T2 X1,
  close_typ_wrt_typ X1 T1 = close_typ_wrt_typ X1 T2 ->
  T1 = T2.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate close_typ_wrt_typ_inj : lngen.

Lemma close_binding_wrt_typ_inj :
forall b1 b2 X1,
  close_binding_wrt_typ X1 b1 = close_binding_wrt_typ X1 b2 ->
  b1 = b2.
Proof.
unfold close_binding_wrt_typ; eauto with lngen.
Qed.

Hint Immediate close_binding_wrt_typ_inj : lngen.

Lemma close_exp_wrt_typ_inj :
forall e1 e2 X1,
  close_exp_wrt_typ X1 e1 = close_exp_wrt_typ X1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

Hint Immediate close_exp_wrt_typ_inj : lngen.

Lemma close_exp_wrt_exp_inj :
forall e1 e2 x1,
  close_exp_wrt_exp x1 e1 = close_exp_wrt_exp x1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate close_exp_wrt_exp_inj : lngen.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall T1 X1 n1,
  X1 `notin` fv_typ_in_typ T1 ->
  close_typ_wrt_typ_rec n1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) T1) = T1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall T1 X1 n1,
  X1 `notin` fv_typ_in_typ T1 ->
  close_typ_wrt_typ_rec n1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) T1) = T1.
Proof.
pose proof close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.
Hint Rewrite close_typ_wrt_typ_rec_open_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_typ_rec_open_binding_wrt_typ_rec_mutual :
(forall b1 X1 n1,
  X1 `notin` fv_typ_in_binding b1 ->
  close_binding_wrt_typ_rec n1 X1 (open_binding_wrt_typ_rec n1 (typ_var_f X1) b1) = b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_typ_rec_open_binding_wrt_typ_rec :
forall b1 X1 n1,
  X1 `notin` fv_typ_in_binding b1 ->
  close_binding_wrt_typ_rec n1 X1 (open_binding_wrt_typ_rec n1 (typ_var_f X1) b1) = b1.
Proof.
pose proof close_binding_wrt_typ_rec_open_binding_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_binding_wrt_typ_rec_open_binding_wrt_typ_rec : lngen.
Hint Rewrite close_binding_wrt_typ_rec_open_binding_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  X1 `notin` fv_typ_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e1 X1 n1,
  X1 `notin` fv_typ_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = e1.
Proof.
pose proof close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.
Hint Rewrite close_exp_wrt_typ_rec_open_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` fv_exp_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 x1 n1,
  x1 `notin` fv_exp_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = e1.
Proof.
pose proof close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.
Hint Rewrite close_exp_wrt_exp_rec_open_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_open_typ_wrt_typ :
forall T1 X1,
  X1 `notin` fv_typ_in_typ T1 ->
  close_typ_wrt_typ X1 (open_typ_wrt_typ T1 (typ_var_f X1)) = T1.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve close_typ_wrt_typ_open_typ_wrt_typ : lngen.
Hint Rewrite close_typ_wrt_typ_open_typ_wrt_typ using solve [auto] : lngen.

Lemma close_binding_wrt_typ_open_binding_wrt_typ :
forall b1 X1,
  X1 `notin` fv_typ_in_binding b1 ->
  close_binding_wrt_typ X1 (open_binding_wrt_typ b1 (typ_var_f X1)) = b1.
Proof.
unfold close_binding_wrt_typ; unfold open_binding_wrt_typ; default_simp.
Qed.

Hint Resolve close_binding_wrt_typ_open_binding_wrt_typ : lngen.
Hint Rewrite close_binding_wrt_typ_open_binding_wrt_typ using solve [auto] : lngen.

Lemma close_exp_wrt_typ_open_exp_wrt_typ :
forall e1 X1,
  X1 `notin` fv_typ_in_exp e1 ->
  close_exp_wrt_typ X1 (open_exp_wrt_typ e1 (typ_var_f X1)) = e1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve close_exp_wrt_typ_open_exp_wrt_typ : lngen.
Hint Rewrite close_exp_wrt_typ_open_exp_wrt_typ using solve [auto] : lngen.

Lemma close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 x1,
  x1 `notin` fv_exp_in_exp e1 ->
  close_exp_wrt_exp x1 (open_exp_wrt_exp e1 (exp_var_f x1)) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve close_exp_wrt_exp_open_exp_wrt_exp : lngen.
Hint Rewrite close_exp_wrt_exp_open_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual :
(forall T1 X1 n1,
  open_typ_wrt_typ_rec n1 (typ_var_f X1) (close_typ_wrt_typ_rec n1 X1 T1) = T1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec :
forall T1 X1 n1,
  open_typ_wrt_typ_rec n1 (typ_var_f X1) (close_typ_wrt_typ_rec n1 X1 T1) = T1.
Proof.
pose proof open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_typ_wrt_typ_rec_close_typ_wrt_typ_rec : lngen.
Hint Rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_typ_rec_close_binding_wrt_typ_rec_mutual :
(forall b1 X1 n1,
  open_binding_wrt_typ_rec n1 (typ_var_f X1) (close_binding_wrt_typ_rec n1 X1 b1) = b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_typ_rec_close_binding_wrt_typ_rec :
forall b1 X1 n1,
  open_binding_wrt_typ_rec n1 (typ_var_f X1) (close_binding_wrt_typ_rec n1 X1 b1) = b1.
Proof.
pose proof open_binding_wrt_typ_rec_close_binding_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_binding_wrt_typ_rec_close_binding_wrt_typ_rec : lngen.
Hint Rewrite open_binding_wrt_typ_rec_close_binding_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  open_exp_wrt_typ_rec n1 (typ_var_f X1) (close_exp_wrt_typ_rec n1 X1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  open_exp_wrt_typ_rec n1 (typ_var_f X1) (close_exp_wrt_typ_rec n1 X1 e1) = e1.
Proof.
pose proof open_exp_wrt_typ_rec_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_typ_rec_close_exp_wrt_typ_rec : lngen.
Hint Rewrite open_exp_wrt_typ_rec_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (exp_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (exp_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1.
Proof.
pose proof open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_exp_rec_close_exp_wrt_exp_rec : lngen.
Hint Rewrite open_exp_wrt_exp_rec_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_close_typ_wrt_typ :
forall T1 X1,
  open_typ_wrt_typ (close_typ_wrt_typ X1 T1) (typ_var_f X1) = T1.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve open_typ_wrt_typ_close_typ_wrt_typ : lngen.
Hint Rewrite open_typ_wrt_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma open_binding_wrt_typ_close_binding_wrt_typ :
forall b1 X1,
  open_binding_wrt_typ (close_binding_wrt_typ X1 b1) (typ_var_f X1) = b1.
Proof.
unfold close_binding_wrt_typ; unfold open_binding_wrt_typ; default_simp.
Qed.

Hint Resolve open_binding_wrt_typ_close_binding_wrt_typ : lngen.
Hint Rewrite open_binding_wrt_typ_close_binding_wrt_typ using solve [auto] : lngen.

Lemma open_exp_wrt_typ_close_exp_wrt_typ :
forall e1 X1,
  open_exp_wrt_typ (close_exp_wrt_typ X1 e1) (typ_var_f X1) = e1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve open_exp_wrt_typ_close_exp_wrt_typ : lngen.
Hint Rewrite open_exp_wrt_typ_close_exp_wrt_typ using solve [auto] : lngen.

Lemma open_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  open_exp_wrt_exp (close_exp_wrt_exp x1 e1) (exp_var_f x1) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve open_exp_wrt_exp_close_exp_wrt_exp : lngen.
Hint Rewrite open_exp_wrt_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj_mutual :
(forall T2 T1 X1 n1,
  X1 `notin` fv_typ_in_typ T2 ->
  X1 `notin` fv_typ_in_typ T1 ->
  open_typ_wrt_typ_rec n1 (typ_var_f X1) T2 = open_typ_wrt_typ_rec n1 (typ_var_f X1) T1 ->
  T2 = T1).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj :
forall T2 T1 X1 n1,
  X1 `notin` fv_typ_in_typ T2 ->
  X1 `notin` fv_typ_in_typ T1 ->
  open_typ_wrt_typ_rec n1 (typ_var_f X1) T2 = open_typ_wrt_typ_rec n1 (typ_var_f X1) T1 ->
  T2 = T1.
Proof.
pose proof open_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_typ_rec_inj_mutual :
(forall b2 b1 X1 n1,
  X1 `notin` fv_typ_in_binding b2 ->
  X1 `notin` fv_typ_in_binding b1 ->
  open_binding_wrt_typ_rec n1 (typ_var_f X1) b2 = open_binding_wrt_typ_rec n1 (typ_var_f X1) b1 ->
  b2 = b1).
Proof.
apply_mutual_ind binding_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_typ_rec_inj :
forall b2 b1 X1 n1,
  X1 `notin` fv_typ_in_binding b2 ->
  X1 `notin` fv_typ_in_binding b1 ->
  open_binding_wrt_typ_rec n1 (typ_var_f X1) b2 = open_binding_wrt_typ_rec n1 (typ_var_f X1) b1 ->
  b2 = b1.
Proof.
pose proof open_binding_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_binding_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_inj_mutual :
(forall e2 e1 X1 n1,
  X1 `notin` fv_typ_in_exp e2 ->
  X1 `notin` fv_typ_in_exp e1 ->
  open_exp_wrt_typ_rec n1 (typ_var_f X1) e2 = open_exp_wrt_typ_rec n1 (typ_var_f X1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_inj :
forall e2 e1 X1 n1,
  X1 `notin` fv_typ_in_exp e2 ->
  X1 `notin` fv_typ_in_exp e1 ->
  open_exp_wrt_typ_rec n1 (typ_var_f X1) e2 = open_exp_wrt_typ_rec n1 (typ_var_f X1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_exp_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` fv_exp_in_exp e2 ->
  x1 `notin` fv_exp_in_exp e1 ->
  open_exp_wrt_exp_rec n1 (exp_var_f x1) e2 = open_exp_wrt_exp_rec n1 (exp_var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fv_exp_in_exp e2 ->
  x1 `notin` fv_exp_in_exp e1 ->
  open_exp_wrt_exp_rec n1 (exp_var_f x1) e2 = open_exp_wrt_exp_rec n1 (exp_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_inj :
forall T2 T1 X1,
  X1 `notin` fv_typ_in_typ T2 ->
  X1 `notin` fv_typ_in_typ T1 ->
  open_typ_wrt_typ T2 (typ_var_f X1) = open_typ_wrt_typ T1 (typ_var_f X1) ->
  T2 = T1.
Proof.
unfold open_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate open_typ_wrt_typ_inj : lngen.

Lemma open_binding_wrt_typ_inj :
forall b2 b1 X1,
  X1 `notin` fv_typ_in_binding b2 ->
  X1 `notin` fv_typ_in_binding b1 ->
  open_binding_wrt_typ b2 (typ_var_f X1) = open_binding_wrt_typ b1 (typ_var_f X1) ->
  b2 = b1.
Proof.
unfold open_binding_wrt_typ; eauto with lngen.
Qed.

Hint Immediate open_binding_wrt_typ_inj : lngen.

Lemma open_exp_wrt_typ_inj :
forall e2 e1 X1,
  X1 `notin` fv_typ_in_exp e2 ->
  X1 `notin` fv_typ_in_exp e1 ->
  open_exp_wrt_typ e2 (typ_var_f X1) = open_exp_wrt_typ e1 (typ_var_f X1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

Hint Immediate open_exp_wrt_typ_inj : lngen.

Lemma open_exp_wrt_exp_inj :
forall e2 e1 x1,
  x1 `notin` fv_exp_in_exp e2 ->
  x1 `notin` fv_exp_in_exp e1 ->
  open_exp_wrt_exp e2 (exp_var_f x1) = open_exp_wrt_exp e1 (exp_var_f x1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate open_exp_wrt_exp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_of_lc_typ_mutual :
(forall T1,
  lc_typ T1 ->
  degree_typ_wrt_typ 0 T1).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_of_lc_typ :
forall T1,
  lc_typ T1 ->
  degree_typ_wrt_typ 0 T1.
Proof.
pose proof degree_typ_wrt_typ_of_lc_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma degree_binding_wrt_typ_of_lc_binding_mutual :
(forall b1,
  lc_binding b1 ->
  degree_binding_wrt_typ 0 b1).
Proof.
apply_mutual_ind lc_binding_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_binding_wrt_typ_of_lc_binding :
forall b1,
  lc_binding b1 ->
  degree_binding_wrt_typ 0 b1.
Proof.
pose proof degree_binding_wrt_typ_of_lc_binding_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_binding_wrt_typ_of_lc_binding : lngen.

(* begin hide *)

Lemma degree_exp_wrt_typ_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_typ 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_typ_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_typ 0 e1.
Proof.
pose proof degree_exp_wrt_typ_of_lc_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_of_lc_exp : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1.
Proof.
pose proof degree_exp_wrt_exp_of_lc_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_of_lc_exp : lngen.

(* begin hide *)

Lemma lc_typ_of_degree_size_mutual :
forall i1,
(forall T1,
  size_typ T1 = i1 ->
  degree_typ_wrt_typ 0 T1 ->
  lc_typ T1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_degree :
forall T1,
  degree_typ_wrt_typ 0 T1 ->
  lc_typ T1.
Proof.
intros T1; intros;
pose proof (lc_typ_of_degree_size_mutual (size_typ T1));
intuition eauto.
Qed.

Hint Resolve lc_typ_of_degree : lngen.

(* begin hide *)

Lemma lc_binding_of_degree_size_mutual :
forall i1,
(forall b1,
  size_binding b1 = i1 ->
  degree_binding_wrt_typ 0 b1 ->
  lc_binding b1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind binding_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_binding_of_degree :
forall b1,
  degree_binding_wrt_typ 0 b1 ->
  lc_binding b1.
Proof.
intros b1; intros;
pose proof (lc_binding_of_degree_size_mutual (size_binding b1));
intuition eauto.
Qed.

Hint Resolve lc_binding_of_degree : lngen.

(* begin hide *)

Lemma lc_exp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_degree :
forall e1,
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1.
Proof.
intros e1; intros;
pose proof (lc_exp_of_degree_size_mutual (size_exp e1));
intuition eauto.
Qed.

Hint Resolve lc_exp_of_degree : lngen.

Ltac typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_typ_wrt_typ_of_lc_typ in J1; clear H
          end).

Ltac binding_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_binding_wrt_typ_of_lc_binding in J1; clear H
          end).

Ltac exp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_exp_wrt_typ_of_lc_exp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_exp_wrt_exp_of_lc_exp in J2; clear H
          end).

Lemma lc_typ_all_exists :
forall X1 T1 T2,
  lc_typ T1 ->
  lc_typ (open_typ_wrt_typ T2 (typ_var_f X1)) ->
  lc_typ (typ_all T1 T2).
Proof.
intros; typ_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_exp_abs_exists :
forall x1 T1 e1,
  lc_typ T1 ->
  lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)) ->
  lc_exp (exp_abs T1 e1).
Proof.
intros; exp_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_exp_tabs_exists :
forall X1 T1 e1,
  lc_typ T1 ->
  lc_exp (open_exp_wrt_typ e1 (typ_var_f X1)) ->
  lc_exp (exp_tabs T1 e1).
Proof.
intros; exp_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_exp_let_exists :
forall x1 e1 e2,
  lc_exp e1 ->
  lc_exp (open_exp_wrt_exp e2 (exp_var_f x1)) ->
  lc_exp (exp_let e1 e2).
Proof.
intros; exp_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_exp_case_exists :
forall x1 y1 e1 e2 e3,
  lc_exp e1 ->
  lc_exp (open_exp_wrt_exp e2 (exp_var_f x1)) ->
  lc_exp (open_exp_wrt_exp e3 (exp_var_f y1)) ->
  lc_exp (exp_case e1 e2 e3).
Proof.
intros; exp_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_typ (typ_all _ _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_typ_all_exists X1) : core.

Hint Extern 1 (lc_exp (exp_abs _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_abs_exists x1) : core.

Hint Extern 1 (lc_exp (exp_tabs _ _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_exp_tabs_exists X1) : core.

Hint Extern 1 (lc_exp (exp_let _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_let_exists x1) : core.

Hint Extern 1 (lc_exp (exp_case _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  let y1 := fresh in
  pick_fresh y1;
  apply (lc_exp_case_exists x1 y1) : core.

Lemma lc_body_typ_wrt_typ :
forall T1 T2,
  body_typ_wrt_typ T1 ->
  lc_typ T2 ->
  lc_typ (open_typ_wrt_typ T1 T2).
Proof.
unfold body_typ_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
typ_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_typ_wrt_typ : lngen.

Lemma lc_body_binding_wrt_typ :
forall b1 T1,
  body_binding_wrt_typ b1 ->
  lc_typ T1 ->
  lc_binding (open_binding_wrt_typ b1 T1).
Proof.
unfold body_binding_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
binding_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_binding_wrt_typ : lngen.

Lemma lc_body_exp_wrt_typ :
forall e1 T1,
  body_exp_wrt_typ e1 ->
  lc_typ T1 ->
  lc_exp (open_exp_wrt_typ e1 T1).
Proof.
unfold body_exp_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
exp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_exp_wrt_typ : lngen.

Lemma lc_body_exp_wrt_exp :
forall e1 e2,
  body_exp_wrt_exp e1 ->
  lc_exp e2 ->
  lc_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold body_exp_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
exp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_exp_wrt_exp : lngen.

Lemma lc_body_typ_all_2 :
forall T1 T2,
  lc_typ (typ_all T1 T2) ->
  body_typ_wrt_typ T2.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_typ_all_2 : lngen.

Lemma lc_body_exp_abs_2 :
forall T1 e1,
  lc_exp (exp_abs T1 e1) ->
  body_exp_wrt_exp e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_exp_abs_2 : lngen.

Lemma lc_body_exp_tabs_2 :
forall T1 e1,
  lc_exp (exp_tabs T1 e1) ->
  body_exp_wrt_typ e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_exp_tabs_2 : lngen.

Lemma lc_body_exp_let_2 :
forall e1 e2,
  lc_exp (exp_let e1 e2) ->
  body_exp_wrt_exp e2.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_exp_let_2 : lngen.

Lemma lc_body_exp_case_2 :
forall e1 e2 e3,
  lc_exp (exp_case e1 e2 e3) ->
  body_exp_wrt_exp e2.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_exp_case_2 : lngen.

Lemma lc_body_exp_case_3 :
forall e1 e2 e3,
  lc_exp (exp_case e1 e2 e3) ->
  body_exp_wrt_exp e3.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_exp_case_3 : lngen.

(* begin hide *)

Lemma lc_typ_unique_mutual :
(forall T1 (proof2 proof3 : lc_typ T1), proof2 = proof3).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_typ_unique :
forall T1 (proof2 proof3 : lc_typ T1), proof2 = proof3.
Proof.
pose proof lc_typ_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_typ_unique : lngen.

(* begin hide *)

Lemma lc_binding_unique_mutual :
(forall b1 (proof2 proof3 : lc_binding b1), proof2 = proof3).
Proof.
apply_mutual_ind lc_binding_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_binding_unique :
forall b1 (proof2 proof3 : lc_binding b1), proof2 = proof3.
Proof.
pose proof lc_binding_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_binding_unique : lngen.

(* begin hide *)

Lemma lc_exp_unique_mutual :
(forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_exp_unique :
forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3.
Proof.
pose proof lc_exp_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_exp_unique : lngen.

(* begin hide *)

Lemma lc_typ_of_lc_set_typ_mutual :
(forall T1, lc_set_typ T1 -> lc_typ T1).
Proof.
apply_mutual_ind lc_set_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_lc_set_typ :
forall T1, lc_set_typ T1 -> lc_typ T1.
Proof.
pose proof lc_typ_of_lc_set_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_typ_of_lc_set_typ : lngen.

(* begin hide *)

Lemma lc_binding_of_lc_set_binding_mutual :
(forall b1, lc_set_binding b1 -> lc_binding b1).
Proof.
apply_mutual_ind lc_set_binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_binding_of_lc_set_binding :
forall b1, lc_set_binding b1 -> lc_binding b1.
Proof.
pose proof lc_binding_of_lc_set_binding_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_binding_of_lc_set_binding : lngen.

(* begin hide *)

Lemma lc_exp_of_lc_set_exp_mutual :
(forall e1, lc_set_exp e1 -> lc_exp e1).
Proof.
apply_mutual_ind lc_set_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_lc_set_exp :
forall e1, lc_set_exp e1 -> lc_exp e1.
Proof.
pose proof lc_exp_of_lc_set_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_exp_of_lc_set_exp : lngen.

(* begin hide *)

Lemma lc_set_typ_of_lc_typ_size_mutual :
forall i1,
(forall T1,
  size_typ T1 = i1 ->
  lc_typ T1 ->
  lc_set_typ T1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_typ_of_lc_typ :
forall T1,
  lc_typ T1 ->
  lc_set_typ T1.
Proof.
intros T1; intros;
pose proof (lc_set_typ_of_lc_typ_size_mutual (size_typ T1));
intuition eauto.
Qed.

Hint Resolve lc_set_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma lc_set_binding_of_lc_binding_size_mutual :
forall i1,
(forall b1,
  size_binding b1 = i1 ->
  lc_binding b1 ->
  lc_set_binding b1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind binding_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_binding_of_lc_binding];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_binding_of_lc_binding :
forall b1,
  lc_binding b1 ->
  lc_set_binding b1.
Proof.
intros b1; intros;
pose proof (lc_set_binding_of_lc_binding_size_mutual (size_binding b1));
intuition eauto.
Qed.

Hint Resolve lc_set_binding_of_lc_binding : lngen.

(* begin hide *)

Lemma lc_set_exp_of_lc_exp_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  lc_exp e1 ->
  lc_set_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_exp_of_lc_exp];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  lc_set_exp e1.
Proof.
intros e1; intros;
pose proof (lc_set_exp_of_lc_exp_size_mutual (size_exp e1));
intuition eauto.
Qed.

Hint Resolve lc_set_exp_of_lc_exp : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall T1 X1 n1,
  degree_typ_wrt_typ n1 T1 ->
  X1 `notin` fv_typ_in_typ T1 ->
  close_typ_wrt_typ_rec n1 X1 T1 = T1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall T1 X1 n1,
  degree_typ_wrt_typ n1 T1 ->
  X1 `notin` fv_typ_in_typ T1 ->
  close_typ_wrt_typ_rec n1 X1 T1 = T1.
Proof.
pose proof close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve close_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
Hint Rewrite close_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_typ_rec_degree_binding_wrt_typ_mutual :
(forall b1 X1 n1,
  degree_binding_wrt_typ n1 b1 ->
  X1 `notin` fv_typ_in_binding b1 ->
  close_binding_wrt_typ_rec n1 X1 b1 = b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_typ_rec_degree_binding_wrt_typ :
forall b1 X1 n1,
  degree_binding_wrt_typ n1 b1 ->
  X1 `notin` fv_typ_in_binding b1 ->
  close_binding_wrt_typ_rec n1 X1 b1 = b1.
Proof.
pose proof close_binding_wrt_typ_rec_degree_binding_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve close_binding_wrt_typ_rec_degree_binding_wrt_typ : lngen.
Hint Rewrite close_binding_wrt_typ_rec_degree_binding_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  X1 `notin` fv_typ_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_degree_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  X1 `notin` fv_typ_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 e1 = e1.
Proof.
pose proof close_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_typ_rec_degree_exp_wrt_typ : lngen.
Hint Rewrite close_exp_wrt_typ_rec_degree_exp_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` fv_exp_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` fv_exp_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1.
Proof.
pose proof close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
Hint Rewrite close_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_lc_typ :
forall T1 X1,
  lc_typ T1 ->
  X1 `notin` fv_typ_in_typ T1 ->
  close_typ_wrt_typ X1 T1 = T1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve close_typ_wrt_typ_lc_typ : lngen.
Hint Rewrite close_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma close_binding_wrt_typ_lc_binding :
forall b1 X1,
  lc_binding b1 ->
  X1 `notin` fv_typ_in_binding b1 ->
  close_binding_wrt_typ X1 b1 = b1.
Proof.
unfold close_binding_wrt_typ; default_simp.
Qed.

Hint Resolve close_binding_wrt_typ_lc_binding : lngen.
Hint Rewrite close_binding_wrt_typ_lc_binding using solve [auto] : lngen.

Lemma close_exp_wrt_typ_lc_exp :
forall e1 X1,
  lc_exp e1 ->
  X1 `notin` fv_typ_in_exp e1 ->
  close_exp_wrt_typ X1 e1 = e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve close_exp_wrt_typ_lc_exp : lngen.
Hint Rewrite close_exp_wrt_typ_lc_exp using solve [auto] : lngen.

Lemma close_exp_wrt_exp_lc_exp :
forall e1 x1,
  lc_exp e1 ->
  x1 `notin` fv_exp_in_exp e1 ->
  close_exp_wrt_exp x1 e1 = e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve close_exp_wrt_exp_lc_exp : lngen.
Hint Rewrite close_exp_wrt_exp_lc_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall T2 T1 n1,
  degree_typ_wrt_typ n1 T2 ->
  open_typ_wrt_typ_rec n1 T1 T2 = T2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall T2 T1 n1,
  degree_typ_wrt_typ n1 T2 ->
  open_typ_wrt_typ_rec n1 T1 T2 = T2.
Proof.
pose proof open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve open_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
Hint Rewrite open_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_typ_rec_degree_binding_wrt_typ_mutual :
(forall b1 T1 n1,
  degree_binding_wrt_typ n1 b1 ->
  open_binding_wrt_typ_rec n1 T1 b1 = b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_typ_rec_degree_binding_wrt_typ :
forall b1 T1 n1,
  degree_binding_wrt_typ n1 b1 ->
  open_binding_wrt_typ_rec n1 T1 b1 = b1.
Proof.
pose proof open_binding_wrt_typ_rec_degree_binding_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve open_binding_wrt_typ_rec_degree_binding_wrt_typ : lngen.
Hint Rewrite open_binding_wrt_typ_rec_degree_binding_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual :
(forall e1 T1 n1,
  degree_exp_wrt_typ n1 e1 ->
  open_exp_wrt_typ_rec n1 T1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_degree_exp_wrt_typ :
forall e1 T1 n1,
  degree_exp_wrt_typ n1 e1 ->
  open_exp_wrt_typ_rec n1 T1 e1 = e1.
Proof.
pose proof open_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_typ_rec_degree_exp_wrt_typ : lngen.
Hint Rewrite open_exp_wrt_typ_rec_degree_exp_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2.
Proof.
pose proof open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
Hint Rewrite open_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_lc_typ :
forall T2 T1,
  lc_typ T2 ->
  open_typ_wrt_typ T2 T1 = T2.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve open_typ_wrt_typ_lc_typ : lngen.
Hint Rewrite open_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma open_binding_wrt_typ_lc_binding :
forall b1 T1,
  lc_binding b1 ->
  open_binding_wrt_typ b1 T1 = b1.
Proof.
unfold open_binding_wrt_typ; default_simp.
Qed.

Hint Resolve open_binding_wrt_typ_lc_binding : lngen.
Hint Rewrite open_binding_wrt_typ_lc_binding using solve [auto] : lngen.

Lemma open_exp_wrt_typ_lc_exp :
forall e1 T1,
  lc_exp e1 ->
  open_exp_wrt_typ e1 T1 = e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve open_exp_wrt_typ_lc_exp : lngen.
Hint Rewrite open_exp_wrt_typ_lc_exp using solve [auto] : lngen.

Lemma open_exp_wrt_exp_lc_exp :
forall e2 e1,
  lc_exp e2 ->
  open_exp_wrt_exp e2 e1 = e2.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve open_exp_wrt_exp_lc_exp : lngen.
Hint Rewrite open_exp_wrt_exp_lc_exp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_typ_in_typ_close_typ_wrt_typ_rec_mutual :
(forall T1 X1 n1,
  fv_typ_in_typ (close_typ_wrt_typ_rec n1 X1 T1) [=] remove X1 (fv_typ_in_typ T1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_typ_close_typ_wrt_typ_rec :
forall T1 X1 n1,
  fv_typ_in_typ (close_typ_wrt_typ_rec n1 X1 T1) [=] remove X1 (fv_typ_in_typ T1).
Proof.
pose proof fv_typ_in_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_typ_close_typ_wrt_typ_rec : lngen.
Hint Rewrite fv_typ_in_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_binding_close_binding_wrt_typ_rec_mutual :
(forall b1 X1 n1,
  fv_typ_in_binding (close_binding_wrt_typ_rec n1 X1 b1) [=] remove X1 (fv_typ_in_binding b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_binding_close_binding_wrt_typ_rec :
forall b1 X1 n1,
  fv_typ_in_binding (close_binding_wrt_typ_rec n1 X1 b1) [=] remove X1 (fv_typ_in_binding b1).
Proof.
pose proof fv_typ_in_binding_close_binding_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_binding_close_binding_wrt_typ_rec : lngen.
Hint Rewrite fv_typ_in_binding_close_binding_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  fv_typ_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] remove X1 (fv_typ_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  fv_typ_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] remove X1 (fv_typ_in_exp e1).
Proof.
pose proof fv_typ_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_exp_close_exp_wrt_typ_rec : lngen.
Hint Rewrite fv_typ_in_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  fv_typ_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] fv_typ_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  fv_typ_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] fv_typ_in_exp e1.
Proof.
pose proof fv_typ_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite fv_typ_in_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  fv_exp_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] fv_exp_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  fv_exp_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] fv_exp_in_exp e1.
Proof.
pose proof fv_exp_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_close_exp_wrt_typ_rec : lngen.
Hint Rewrite fv_exp_in_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  fv_exp_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (fv_exp_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  fv_exp_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (fv_exp_in_exp e1).
Proof.
pose proof fv_exp_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite fv_exp_in_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_typ_in_typ_close_typ_wrt_typ :
forall T1 X1,
  fv_typ_in_typ (close_typ_wrt_typ X1 T1) [=] remove X1 (fv_typ_in_typ T1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve fv_typ_in_typ_close_typ_wrt_typ : lngen.
Hint Rewrite fv_typ_in_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma fv_typ_in_binding_close_binding_wrt_typ :
forall b1 X1,
  fv_typ_in_binding (close_binding_wrt_typ X1 b1) [=] remove X1 (fv_typ_in_binding b1).
Proof.
unfold close_binding_wrt_typ; default_simp.
Qed.

Hint Resolve fv_typ_in_binding_close_binding_wrt_typ : lngen.
Hint Rewrite fv_typ_in_binding_close_binding_wrt_typ using solve [auto] : lngen.

Lemma fv_typ_in_exp_close_exp_wrt_typ :
forall e1 X1,
  fv_typ_in_exp (close_exp_wrt_typ X1 e1) [=] remove X1 (fv_typ_in_exp e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve fv_typ_in_exp_close_exp_wrt_typ : lngen.
Hint Rewrite fv_typ_in_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma fv_typ_in_exp_close_exp_wrt_exp :
forall e1 x1,
  fv_typ_in_exp (close_exp_wrt_exp x1 e1) [=] fv_typ_in_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_typ_in_exp_close_exp_wrt_exp : lngen.
Hint Rewrite fv_typ_in_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma fv_exp_in_exp_close_exp_wrt_typ :
forall e1 X1,
  fv_exp_in_exp (close_exp_wrt_typ X1 e1) [=] fv_exp_in_exp e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve fv_exp_in_exp_close_exp_wrt_typ : lngen.
Hint Rewrite fv_exp_in_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma fv_exp_in_exp_close_exp_wrt_exp :
forall e1 x1,
  fv_exp_in_exp (close_exp_wrt_exp x1 e1) [=] remove x1 (fv_exp_in_exp e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_exp_in_exp_close_exp_wrt_exp : lngen.
Hint Rewrite fv_exp_in_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma fv_typ_in_typ_open_typ_wrt_typ_rec_lower_mutual :
(forall T1 T2 n1,
  fv_typ_in_typ T1 [<=] fv_typ_in_typ (open_typ_wrt_typ_rec n1 T2 T1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_typ_open_typ_wrt_typ_rec_lower :
forall T1 T2 n1,
  fv_typ_in_typ T1 [<=] fv_typ_in_typ (open_typ_wrt_typ_rec n1 T2 T1).
Proof.
pose proof fv_typ_in_typ_open_typ_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_typ_open_typ_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_binding_open_binding_wrt_typ_rec_lower_mutual :
(forall b1 T1 n1,
  fv_typ_in_binding b1 [<=] fv_typ_in_binding (open_binding_wrt_typ_rec n1 T1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_binding_open_binding_wrt_typ_rec_lower :
forall b1 T1 n1,
  fv_typ_in_binding b1 [<=] fv_typ_in_binding (open_binding_wrt_typ_rec n1 T1 b1).
Proof.
pose proof fv_typ_in_binding_open_binding_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_binding_open_binding_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall e1 T1 n1,
  fv_typ_in_exp e1 [<=] fv_typ_in_exp (open_exp_wrt_typ_rec n1 T1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_exp_open_exp_wrt_typ_rec_lower :
forall e1 T1 n1,
  fv_typ_in_exp e1 [<=] fv_typ_in_exp (open_exp_wrt_typ_rec n1 T1 e1).
Proof.
pose proof fv_typ_in_exp_open_exp_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_exp_open_exp_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  fv_typ_in_exp e1 [<=] fv_typ_in_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  fv_typ_in_exp e1 [<=] fv_typ_in_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof fv_typ_in_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall e1 T1 n1,
  fv_exp_in_exp e1 [<=] fv_exp_in_exp (open_exp_wrt_typ_rec n1 T1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_open_exp_wrt_typ_rec_lower :
forall e1 T1 n1,
  fv_exp_in_exp e1 [<=] fv_exp_in_exp (open_exp_wrt_typ_rec n1 T1 e1).
Proof.
pose proof fv_exp_in_exp_open_exp_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_open_exp_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  fv_exp_in_exp e1 [<=] fv_exp_in_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  fv_exp_in_exp e1 [<=] fv_exp_in_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof fv_exp_in_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

Lemma fv_typ_in_typ_open_typ_wrt_typ_lower :
forall T1 T2,
  fv_typ_in_typ T1 [<=] fv_typ_in_typ (open_typ_wrt_typ T1 T2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve fv_typ_in_typ_open_typ_wrt_typ_lower : lngen.

Lemma fv_typ_in_binding_open_binding_wrt_typ_lower :
forall b1 T1,
  fv_typ_in_binding b1 [<=] fv_typ_in_binding (open_binding_wrt_typ b1 T1).
Proof.
unfold open_binding_wrt_typ; default_simp.
Qed.

Hint Resolve fv_typ_in_binding_open_binding_wrt_typ_lower : lngen.

Lemma fv_typ_in_exp_open_exp_wrt_typ_lower :
forall e1 T1,
  fv_typ_in_exp e1 [<=] fv_typ_in_exp (open_exp_wrt_typ e1 T1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve fv_typ_in_exp_open_exp_wrt_typ_lower : lngen.

Lemma fv_typ_in_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  fv_typ_in_exp e1 [<=] fv_typ_in_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_typ_in_exp_open_exp_wrt_exp_lower : lngen.

Lemma fv_exp_in_exp_open_exp_wrt_typ_lower :
forall e1 T1,
  fv_exp_in_exp e1 [<=] fv_exp_in_exp (open_exp_wrt_typ e1 T1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve fv_exp_in_exp_open_exp_wrt_typ_lower : lngen.

Lemma fv_exp_in_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  fv_exp_in_exp e1 [<=] fv_exp_in_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_exp_in_exp_open_exp_wrt_exp_lower : lngen.

(* begin hide *)

Lemma fv_typ_in_typ_open_typ_wrt_typ_rec_upper_mutual :
(forall T1 T2 n1,
  fv_typ_in_typ (open_typ_wrt_typ_rec n1 T2 T1) [<=] fv_typ_in_typ T2 `union` fv_typ_in_typ T1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_typ_open_typ_wrt_typ_rec_upper :
forall T1 T2 n1,
  fv_typ_in_typ (open_typ_wrt_typ_rec n1 T2 T1) [<=] fv_typ_in_typ T2 `union` fv_typ_in_typ T1.
Proof.
pose proof fv_typ_in_typ_open_typ_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_typ_open_typ_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_binding_open_binding_wrt_typ_rec_upper_mutual :
(forall b1 T1 n1,
  fv_typ_in_binding (open_binding_wrt_typ_rec n1 T1 b1) [<=] fv_typ_in_typ T1 `union` fv_typ_in_binding b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_binding_open_binding_wrt_typ_rec_upper :
forall b1 T1 n1,
  fv_typ_in_binding (open_binding_wrt_typ_rec n1 T1 b1) [<=] fv_typ_in_typ T1 `union` fv_typ_in_binding b1.
Proof.
pose proof fv_typ_in_binding_open_binding_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_binding_open_binding_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall e1 T1 n1,
  fv_typ_in_exp (open_exp_wrt_typ_rec n1 T1 e1) [<=] fv_typ_in_typ T1 `union` fv_typ_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_exp_open_exp_wrt_typ_rec_upper :
forall e1 T1 n1,
  fv_typ_in_exp (open_exp_wrt_typ_rec n1 T1 e1) [<=] fv_typ_in_typ T1 `union` fv_typ_in_exp e1.
Proof.
pose proof fv_typ_in_exp_open_exp_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_exp_open_exp_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  fv_typ_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fv_typ_in_exp e2 `union` fv_typ_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_typ_in_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  fv_typ_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fv_typ_in_exp e2 `union` fv_typ_in_exp e1.
Proof.
pose proof fv_typ_in_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall e1 T1 n1,
  fv_exp_in_exp (open_exp_wrt_typ_rec n1 T1 e1) [<=] fv_exp_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_open_exp_wrt_typ_rec_upper :
forall e1 T1 n1,
  fv_exp_in_exp (open_exp_wrt_typ_rec n1 T1 e1) [<=] fv_exp_in_exp e1.
Proof.
pose proof fv_exp_in_exp_open_exp_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_open_exp_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  fv_exp_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fv_exp_in_exp e2 `union` fv_exp_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  fv_exp_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fv_exp_in_exp e2 `union` fv_exp_in_exp e1.
Proof.
pose proof fv_exp_in_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

Lemma fv_typ_in_typ_open_typ_wrt_typ_upper :
forall T1 T2,
  fv_typ_in_typ (open_typ_wrt_typ T1 T2) [<=] fv_typ_in_typ T2 `union` fv_typ_in_typ T1.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve fv_typ_in_typ_open_typ_wrt_typ_upper : lngen.

Lemma fv_typ_in_binding_open_binding_wrt_typ_upper :
forall b1 T1,
  fv_typ_in_binding (open_binding_wrt_typ b1 T1) [<=] fv_typ_in_typ T1 `union` fv_typ_in_binding b1.
Proof.
unfold open_binding_wrt_typ; default_simp.
Qed.

Hint Resolve fv_typ_in_binding_open_binding_wrt_typ_upper : lngen.

Lemma fv_typ_in_exp_open_exp_wrt_typ_upper :
forall e1 T1,
  fv_typ_in_exp (open_exp_wrt_typ e1 T1) [<=] fv_typ_in_typ T1 `union` fv_typ_in_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve fv_typ_in_exp_open_exp_wrt_typ_upper : lngen.

Lemma fv_typ_in_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  fv_typ_in_exp (open_exp_wrt_exp e1 e2) [<=] fv_typ_in_exp e2 `union` fv_typ_in_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_typ_in_exp_open_exp_wrt_exp_upper : lngen.

Lemma fv_exp_in_exp_open_exp_wrt_typ_upper :
forall e1 T1,
  fv_exp_in_exp (open_exp_wrt_typ e1 T1) [<=] fv_exp_in_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve fv_exp_in_exp_open_exp_wrt_typ_upper : lngen.

Lemma fv_exp_in_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  fv_exp_in_exp (open_exp_wrt_exp e1 e2) [<=] fv_exp_in_exp e2 `union` fv_exp_in_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_exp_in_exp_open_exp_wrt_exp_upper : lngen.

(* begin hide *)

Lemma fv_typ_in_typ_subst_typ_in_typ_fresh_mutual :
(forall T1 T2 X1,
  X1 `notin` fv_typ_in_typ T1 ->
  fv_typ_in_typ (subst_typ_in_typ T2 X1 T1) [=] fv_typ_in_typ T1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_in_typ_subst_typ_in_typ_fresh :
forall T1 T2 X1,
  X1 `notin` fv_typ_in_typ T1 ->
  fv_typ_in_typ (subst_typ_in_typ T2 X1 T1) [=] fv_typ_in_typ T1.
Proof.
pose proof fv_typ_in_typ_subst_typ_in_typ_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_typ_subst_typ_in_typ_fresh : lngen.
Hint Rewrite fv_typ_in_typ_subst_typ_in_typ_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_typ_in_binding_subst_typ_in_binding_fresh_mutual :
(forall b1 T1 X1,
  X1 `notin` fv_typ_in_binding b1 ->
  fv_typ_in_binding (subst_typ_in_binding T1 X1 b1) [=] fv_typ_in_binding b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_in_binding_subst_typ_in_binding_fresh :
forall b1 T1 X1,
  X1 `notin` fv_typ_in_binding b1 ->
  fv_typ_in_binding (subst_typ_in_binding T1 X1 b1) [=] fv_typ_in_binding b1.
Proof.
pose proof fv_typ_in_binding_subst_typ_in_binding_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_binding_subst_typ_in_binding_fresh : lngen.
Hint Rewrite fv_typ_in_binding_subst_typ_in_binding_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_typ_in_exp_subst_typ_in_exp_fresh_mutual :
(forall e1 T1 X1,
  X1 `notin` fv_typ_in_exp e1 ->
  fv_typ_in_exp (subst_typ_in_exp T1 X1 e1) [=] fv_typ_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_in_exp_subst_typ_in_exp_fresh :
forall e1 T1 X1,
  X1 `notin` fv_typ_in_exp e1 ->
  fv_typ_in_exp (subst_typ_in_exp T1 X1 e1) [=] fv_typ_in_exp e1.
Proof.
pose proof fv_typ_in_exp_subst_typ_in_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_exp_subst_typ_in_exp_fresh : lngen.
Hint Rewrite fv_typ_in_exp_subst_typ_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_typ_in_exp_subst_exp_in_exp_fresh_mutual :
(forall e1 T1 X1,
  fv_exp_in_exp (subst_typ_in_exp T1 X1 e1) [=] fv_exp_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_in_exp_subst_exp_in_exp_fresh :
forall e1 T1 X1,
  fv_exp_in_exp (subst_typ_in_exp T1 X1 e1) [=] fv_exp_in_exp e1.
Proof.
pose proof fv_typ_in_exp_subst_exp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_exp_subst_exp_in_exp_fresh : lngen.
Hint Rewrite fv_typ_in_exp_subst_exp_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_exp_in_exp_subst_exp_in_exp_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` fv_exp_in_exp e1 ->
  fv_exp_in_exp (subst_exp_in_exp e2 x1 e1) [=] fv_exp_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_in_exp_subst_exp_in_exp_fresh :
forall e1 e2 x1,
  x1 `notin` fv_exp_in_exp e1 ->
  fv_exp_in_exp (subst_exp_in_exp e2 x1 e1) [=] fv_exp_in_exp e1.
Proof.
pose proof fv_exp_in_exp_subst_exp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_subst_exp_in_exp_fresh : lngen.
Hint Rewrite fv_exp_in_exp_subst_exp_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_typ_in_typ_subst_typ_in_typ_lower_mutual :
(forall T1 T2 X1,
  remove X1 (fv_typ_in_typ T1) [<=] fv_typ_in_typ (subst_typ_in_typ T2 X1 T1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_in_typ_subst_typ_in_typ_lower :
forall T1 T2 X1,
  remove X1 (fv_typ_in_typ T1) [<=] fv_typ_in_typ (subst_typ_in_typ T2 X1 T1).
Proof.
pose proof fv_typ_in_typ_subst_typ_in_typ_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_typ_subst_typ_in_typ_lower : lngen.

(* begin hide *)

Lemma fv_typ_in_binding_subst_typ_in_binding_lower_mutual :
(forall b1 T1 X1,
  remove X1 (fv_typ_in_binding b1) [<=] fv_typ_in_binding (subst_typ_in_binding T1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_in_binding_subst_typ_in_binding_lower :
forall b1 T1 X1,
  remove X1 (fv_typ_in_binding b1) [<=] fv_typ_in_binding (subst_typ_in_binding T1 X1 b1).
Proof.
pose proof fv_typ_in_binding_subst_typ_in_binding_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_binding_subst_typ_in_binding_lower : lngen.

(* begin hide *)

Lemma fv_typ_in_exp_subst_typ_in_exp_lower_mutual :
(forall e1 T1 X1,
  remove X1 (fv_typ_in_exp e1) [<=] fv_typ_in_exp (subst_typ_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_in_exp_subst_typ_in_exp_lower :
forall e1 T1 X1,
  remove X1 (fv_typ_in_exp e1) [<=] fv_typ_in_exp (subst_typ_in_exp T1 X1 e1).
Proof.
pose proof fv_typ_in_exp_subst_typ_in_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_exp_subst_typ_in_exp_lower : lngen.

(* begin hide *)

Lemma fv_typ_in_exp_subst_exp_in_exp_lower_mutual :
(forall e1 e2 x1,
  fv_typ_in_exp e1 [<=] fv_typ_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_in_exp_subst_exp_in_exp_lower :
forall e1 e2 x1,
  fv_typ_in_exp e1 [<=] fv_typ_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof fv_typ_in_exp_subst_exp_in_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_exp_subst_exp_in_exp_lower : lngen.

(* begin hide *)

Lemma fv_exp_in_exp_subst_typ_in_exp_lower_mutual :
(forall e1 T1 X1,
  fv_exp_in_exp e1 [<=] fv_exp_in_exp (subst_typ_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_in_exp_subst_typ_in_exp_lower :
forall e1 T1 X1,
  fv_exp_in_exp e1 [<=] fv_exp_in_exp (subst_typ_in_exp T1 X1 e1).
Proof.
pose proof fv_exp_in_exp_subst_typ_in_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_subst_typ_in_exp_lower : lngen.

(* begin hide *)

Lemma fv_exp_in_exp_subst_exp_in_exp_lower_mutual :
(forall e1 e2 x1,
  remove x1 (fv_exp_in_exp e1) [<=] fv_exp_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_in_exp_subst_exp_in_exp_lower :
forall e1 e2 x1,
  remove x1 (fv_exp_in_exp e1) [<=] fv_exp_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof fv_exp_in_exp_subst_exp_in_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_subst_exp_in_exp_lower : lngen.

(* begin hide *)

Lemma fv_typ_in_typ_subst_typ_in_typ_notin_mutual :
(forall T1 T2 X1 X2,
  X2 `notin` fv_typ_in_typ T1 ->
  X2 `notin` fv_typ_in_typ T2 ->
  X2 `notin` fv_typ_in_typ (subst_typ_in_typ T2 X1 T1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_in_typ_subst_typ_in_typ_notin :
forall T1 T2 X1 X2,
  X2 `notin` fv_typ_in_typ T1 ->
  X2 `notin` fv_typ_in_typ T2 ->
  X2 `notin` fv_typ_in_typ (subst_typ_in_typ T2 X1 T1).
Proof.
pose proof fv_typ_in_typ_subst_typ_in_typ_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_typ_subst_typ_in_typ_notin : lngen.

(* begin hide *)

Lemma fv_typ_in_binding_subst_typ_in_binding_notin_mutual :
(forall b1 T1 X1 X2,
  X2 `notin` fv_typ_in_binding b1 ->
  X2 `notin` fv_typ_in_typ T1 ->
  X2 `notin` fv_typ_in_binding (subst_typ_in_binding T1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_in_binding_subst_typ_in_binding_notin :
forall b1 T1 X1 X2,
  X2 `notin` fv_typ_in_binding b1 ->
  X2 `notin` fv_typ_in_typ T1 ->
  X2 `notin` fv_typ_in_binding (subst_typ_in_binding T1 X1 b1).
Proof.
pose proof fv_typ_in_binding_subst_typ_in_binding_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_binding_subst_typ_in_binding_notin : lngen.

(* begin hide *)

Lemma fv_typ_in_exp_subst_typ_in_exp_notin_mutual :
(forall e1 T1 X1 X2,
  X2 `notin` fv_typ_in_exp e1 ->
  X2 `notin` fv_typ_in_typ T1 ->
  X2 `notin` fv_typ_in_exp (subst_typ_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_in_exp_subst_typ_in_exp_notin :
forall e1 T1 X1 X2,
  X2 `notin` fv_typ_in_exp e1 ->
  X2 `notin` fv_typ_in_typ T1 ->
  X2 `notin` fv_typ_in_exp (subst_typ_in_exp T1 X1 e1).
Proof.
pose proof fv_typ_in_exp_subst_typ_in_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_exp_subst_typ_in_exp_notin : lngen.

(* begin hide *)

Lemma fv_typ_in_exp_subst_exp_in_exp_notin_mutual :
(forall e1 e2 x1 X1,
  X1 `notin` fv_typ_in_exp e1 ->
  X1 `notin` fv_typ_in_exp e2 ->
  X1 `notin` fv_typ_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_in_exp_subst_exp_in_exp_notin :
forall e1 e2 x1 X1,
  X1 `notin` fv_typ_in_exp e1 ->
  X1 `notin` fv_typ_in_exp e2 ->
  X1 `notin` fv_typ_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof fv_typ_in_exp_subst_exp_in_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_exp_subst_exp_in_exp_notin : lngen.

(* begin hide *)

Lemma fv_exp_in_exp_subst_typ_in_exp_notin_mutual :
(forall e1 T1 X1 x1,
  x1 `notin` fv_exp_in_exp e1 ->
  x1 `notin` fv_exp_in_exp (subst_typ_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_in_exp_subst_typ_in_exp_notin :
forall e1 T1 X1 x1,
  x1 `notin` fv_exp_in_exp e1 ->
  x1 `notin` fv_exp_in_exp (subst_typ_in_exp T1 X1 e1).
Proof.
pose proof fv_exp_in_exp_subst_typ_in_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_subst_typ_in_exp_notin : lngen.

(* begin hide *)

Lemma fv_exp_in_exp_subst_exp_in_exp_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` fv_exp_in_exp e1 ->
  x2 `notin` fv_exp_in_exp e2 ->
  x2 `notin` fv_exp_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_in_exp_subst_exp_in_exp_notin :
forall e1 e2 x1 x2,
  x2 `notin` fv_exp_in_exp e1 ->
  x2 `notin` fv_exp_in_exp e2 ->
  x2 `notin` fv_exp_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof fv_exp_in_exp_subst_exp_in_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_subst_exp_in_exp_notin : lngen.

(* begin hide *)

Lemma fv_typ_in_typ_subst_typ_in_typ_upper_mutual :
(forall T1 T2 X1,
  fv_typ_in_typ (subst_typ_in_typ T2 X1 T1) [<=] fv_typ_in_typ T2 `union` remove X1 (fv_typ_in_typ T1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_in_typ_subst_typ_in_typ_upper :
forall T1 T2 X1,
  fv_typ_in_typ (subst_typ_in_typ T2 X1 T1) [<=] fv_typ_in_typ T2 `union` remove X1 (fv_typ_in_typ T1).
Proof.
pose proof fv_typ_in_typ_subst_typ_in_typ_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_typ_subst_typ_in_typ_upper : lngen.

(* begin hide *)

Lemma fv_typ_in_binding_subst_typ_in_binding_upper_mutual :
(forall b1 T1 X1,
  fv_typ_in_binding (subst_typ_in_binding T1 X1 b1) [<=] fv_typ_in_typ T1 `union` remove X1 (fv_typ_in_binding b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_in_binding_subst_typ_in_binding_upper :
forall b1 T1 X1,
  fv_typ_in_binding (subst_typ_in_binding T1 X1 b1) [<=] fv_typ_in_typ T1 `union` remove X1 (fv_typ_in_binding b1).
Proof.
pose proof fv_typ_in_binding_subst_typ_in_binding_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_binding_subst_typ_in_binding_upper : lngen.

(* begin hide *)

Lemma fv_typ_in_exp_subst_typ_in_exp_upper_mutual :
(forall e1 T1 X1,
  fv_typ_in_exp (subst_typ_in_exp T1 X1 e1) [<=] fv_typ_in_typ T1 `union` remove X1 (fv_typ_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_in_exp_subst_typ_in_exp_upper :
forall e1 T1 X1,
  fv_typ_in_exp (subst_typ_in_exp T1 X1 e1) [<=] fv_typ_in_typ T1 `union` remove X1 (fv_typ_in_exp e1).
Proof.
pose proof fv_typ_in_exp_subst_typ_in_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_exp_subst_typ_in_exp_upper : lngen.

(* begin hide *)

Lemma fv_typ_in_exp_subst_exp_in_exp_upper_mutual :
(forall e1 e2 x1,
  fv_typ_in_exp (subst_exp_in_exp e2 x1 e1) [<=] fv_typ_in_exp e2 `union` fv_typ_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_in_exp_subst_exp_in_exp_upper :
forall e1 e2 x1,
  fv_typ_in_exp (subst_exp_in_exp e2 x1 e1) [<=] fv_typ_in_exp e2 `union` fv_typ_in_exp e1.
Proof.
pose proof fv_typ_in_exp_subst_exp_in_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_in_exp_subst_exp_in_exp_upper : lngen.

(* begin hide *)

Lemma fv_exp_in_exp_subst_typ_in_exp_upper_mutual :
(forall e1 T1 X1,
  fv_exp_in_exp (subst_typ_in_exp T1 X1 e1) [<=] fv_exp_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_in_exp_subst_typ_in_exp_upper :
forall e1 T1 X1,
  fv_exp_in_exp (subst_typ_in_exp T1 X1 e1) [<=] fv_exp_in_exp e1.
Proof.
pose proof fv_exp_in_exp_subst_typ_in_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_subst_typ_in_exp_upper : lngen.

(* begin hide *)

Lemma fv_exp_in_exp_subst_exp_in_exp_upper_mutual :
(forall e1 e2 x1,
  fv_exp_in_exp (subst_exp_in_exp e2 x1 e1) [<=] fv_exp_in_exp e2 `union` remove x1 (fv_exp_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_in_exp_subst_exp_in_exp_upper :
forall e1 e2 x1,
  fv_exp_in_exp (subst_exp_in_exp e2 x1 e1) [<=] fv_exp_in_exp e2 `union` remove x1 (fv_exp_in_exp e1).
Proof.
pose proof fv_exp_in_exp_subst_exp_in_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_subst_exp_in_exp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_rec_mutual :
(forall T2 T1 X1 X2 n1,
  degree_typ_wrt_typ n1 T1 ->
  X1 <> X2 ->
  X2 `notin` fv_typ_in_typ T1 ->
  subst_typ_in_typ T1 X1 (close_typ_wrt_typ_rec n1 X2 T2) = close_typ_wrt_typ_rec n1 X2 (subst_typ_in_typ T1 X1 T2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_rec :
forall T2 T1 X1 X2 n1,
  degree_typ_wrt_typ n1 T1 ->
  X1 <> X2 ->
  X2 `notin` fv_typ_in_typ T1 ->
  subst_typ_in_typ T1 X1 (close_typ_wrt_typ_rec n1 X2 T2) = close_typ_wrt_typ_rec n1 X2 (subst_typ_in_typ T1 X1 T2).
Proof.
pose proof subst_typ_in_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_typ_close_typ_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_binding_close_binding_wrt_typ_rec_mutual :
(forall b1 T1 X1 X2 n1,
  degree_typ_wrt_typ n1 T1 ->
  X1 <> X2 ->
  X2 `notin` fv_typ_in_typ T1 ->
  subst_typ_in_binding T1 X1 (close_binding_wrt_typ_rec n1 X2 b1) = close_binding_wrt_typ_rec n1 X2 (subst_typ_in_binding T1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_binding_close_binding_wrt_typ_rec :
forall b1 T1 X1 X2 n1,
  degree_typ_wrt_typ n1 T1 ->
  X1 <> X2 ->
  X2 `notin` fv_typ_in_typ T1 ->
  subst_typ_in_binding T1 X1 (close_binding_wrt_typ_rec n1 X2 b1) = close_binding_wrt_typ_rec n1 X2 (subst_typ_in_binding T1 X1 b1).
Proof.
pose proof subst_typ_in_binding_close_binding_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_binding_close_binding_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 T1 X1 X2 n1,
  degree_typ_wrt_typ n1 T1 ->
  X1 <> X2 ->
  X2 `notin` fv_typ_in_typ T1 ->
  subst_typ_in_exp T1 X1 (close_exp_wrt_typ_rec n1 X2 e1) = close_exp_wrt_typ_rec n1 X2 (subst_typ_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_close_exp_wrt_typ_rec :
forall e1 T1 X1 X2 n1,
  degree_typ_wrt_typ n1 T1 ->
  X1 <> X2 ->
  X2 `notin` fv_typ_in_typ T1 ->
  subst_typ_in_exp T1 X1 (close_exp_wrt_typ_rec n1 X2 e1) = close_exp_wrt_typ_rec n1 X2 (subst_typ_in_exp T1 X1 e1).
Proof.
pose proof subst_typ_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_exp_close_exp_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 T1 x1 X1 n1,
  subst_typ_in_exp T1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (subst_typ_in_exp T1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_close_exp_wrt_exp_rec :
forall e1 T1 x1 X1 n1,
  subst_typ_in_exp T1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (subst_typ_in_exp T1 x1 e1).
Proof.
pose proof subst_typ_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_exp_close_exp_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_typ_rec_mutual :
(forall e2 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` fv_typ_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_typ_rec n1 x1 e2) = close_exp_wrt_typ_rec n1 x1 (subst_exp_in_exp e1 X1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_close_exp_wrt_typ_rec :
forall e2 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` fv_typ_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_typ_rec n1 x1 e2) = close_exp_wrt_typ_rec n1 x1 (subst_exp_in_exp e1 X1 e2).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_close_exp_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_exp_in_exp e1 ->
  subst_exp_in_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_exp_in_exp e1 ->
  subst_exp_in_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_close_exp_wrt_exp_rec : lngen.

Lemma subst_typ_in_typ_close_typ_wrt_typ :
forall T2 T1 X1 X2,
  lc_typ T1 ->  X1 <> X2 ->
  X2 `notin` fv_typ_in_typ T1 ->
  subst_typ_in_typ T1 X1 (close_typ_wrt_typ X2 T2) = close_typ_wrt_typ X2 (subst_typ_in_typ T1 X1 T2).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_typ_close_typ_wrt_typ : lngen.

Lemma subst_typ_in_binding_close_binding_wrt_typ :
forall b1 T1 X1 X2,
  lc_typ T1 ->  X1 <> X2 ->
  X2 `notin` fv_typ_in_typ T1 ->
  subst_typ_in_binding T1 X1 (close_binding_wrt_typ X2 b1) = close_binding_wrt_typ X2 (subst_typ_in_binding T1 X1 b1).
Proof.
unfold close_binding_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_binding_close_binding_wrt_typ : lngen.

Lemma subst_typ_in_exp_close_exp_wrt_typ :
forall e1 T1 X1 X2,
  lc_typ T1 ->  X1 <> X2 ->
  X2 `notin` fv_typ_in_typ T1 ->
  subst_typ_in_exp T1 X1 (close_exp_wrt_typ X2 e1) = close_exp_wrt_typ X2 (subst_typ_in_exp T1 X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_exp_close_exp_wrt_typ : lngen.

Lemma subst_typ_in_exp_close_exp_wrt_exp :
forall e1 T1 x1 X1,
  lc_typ T1 ->  subst_typ_in_exp T1 x1 (close_exp_wrt_exp X1 e1) = close_exp_wrt_exp X1 (subst_typ_in_exp T1 x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_typ_in_exp_close_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_typ :
forall e2 e1 X1 x1,
  lc_exp e1 ->  x1 `notin` fv_typ_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_typ x1 e2) = close_exp_wrt_typ x1 (subst_exp_in_exp e1 X1 e2).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_close_exp_wrt_typ : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_exp :
forall e2 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fv_exp_in_exp e1 ->
  subst_exp_in_exp e1 x1 (close_exp_wrt_exp x2 e2) = close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 e2).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_degree_typ_wrt_typ_mutual :
(forall T1 T2 X1 n1,
  degree_typ_wrt_typ n1 T1 ->
  degree_typ_wrt_typ n1 T2 ->
  degree_typ_wrt_typ n1 (subst_typ_in_typ T2 X1 T1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_degree_typ_wrt_typ :
forall T1 T2 X1 n1,
  degree_typ_wrt_typ n1 T1 ->
  degree_typ_wrt_typ n1 T2 ->
  degree_typ_wrt_typ n1 (subst_typ_in_typ T2 X1 T1).
Proof.
pose proof subst_typ_in_typ_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_typ_degree_typ_wrt_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_binding_degree_binding_wrt_typ_mutual :
(forall b1 T1 X1 n1,
  degree_binding_wrt_typ n1 b1 ->
  degree_typ_wrt_typ n1 T1 ->
  degree_binding_wrt_typ n1 (subst_typ_in_binding T1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_binding_degree_binding_wrt_typ :
forall b1 T1 X1 n1,
  degree_binding_wrt_typ n1 b1 ->
  degree_typ_wrt_typ n1 T1 ->
  degree_binding_wrt_typ n1 (subst_typ_in_binding T1 X1 b1).
Proof.
pose proof subst_typ_in_binding_degree_binding_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_binding_degree_binding_wrt_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_degree_exp_wrt_typ_mutual :
(forall e1 T1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 T1 ->
  degree_exp_wrt_typ n1 (subst_typ_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_degree_exp_wrt_typ :
forall e1 T1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 T1 ->
  degree_exp_wrt_typ n1 (subst_typ_in_exp T1 X1 e1).
Proof.
pose proof subst_typ_in_exp_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_exp_degree_exp_wrt_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_degree_exp_wrt_exp_mutual :
(forall e1 T1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_typ_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_degree_exp_wrt_exp :
forall e1 T1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_typ_in_exp T1 X1 e1).
Proof.
pose proof subst_typ_in_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_typ_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_typ :
forall e1 e2 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_degree_exp_wrt_typ : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_exp_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_exp :
forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_fresh_eq_mutual :
(forall T2 T1 X1,
  X1 `notin` fv_typ_in_typ T2 ->
  subst_typ_in_typ T1 X1 T2 = T2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_fresh_eq :
forall T2 T1 X1,
  X1 `notin` fv_typ_in_typ T2 ->
  subst_typ_in_typ T1 X1 T2 = T2.
Proof.
pose proof subst_typ_in_typ_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_typ_fresh_eq : lngen.
Hint Rewrite subst_typ_in_typ_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_binding_fresh_eq_mutual :
(forall b1 T1 X1,
  X1 `notin` fv_typ_in_binding b1 ->
  subst_typ_in_binding T1 X1 b1 = b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_binding_fresh_eq :
forall b1 T1 X1,
  X1 `notin` fv_typ_in_binding b1 ->
  subst_typ_in_binding T1 X1 b1 = b1.
Proof.
pose proof subst_typ_in_binding_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_binding_fresh_eq : lngen.
Hint Rewrite subst_typ_in_binding_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_fresh_eq_mutual :
(forall e1 T1 X1,
  X1 `notin` fv_typ_in_exp e1 ->
  subst_typ_in_exp T1 X1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_fresh_eq :
forall e1 T1 X1,
  X1 `notin` fv_typ_in_exp e1 ->
  subst_typ_in_exp T1 X1 e1 = e1.
Proof.
pose proof subst_typ_in_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_exp_fresh_eq : lngen.
Hint Rewrite subst_typ_in_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_exp_in_exp e2 ->
  subst_exp_in_exp e1 x1 e2 = e2).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fv_exp_in_exp e2 ->
  subst_exp_in_exp e1 x1 e2 = e2.
Proof.
pose proof subst_exp_in_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_fresh_eq : lngen.
Hint Rewrite subst_exp_in_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_fresh_same_mutual :
(forall T2 T1 X1,
  X1 `notin` fv_typ_in_typ T1 ->
  X1 `notin` fv_typ_in_typ (subst_typ_in_typ T1 X1 T2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_fresh_same :
forall T2 T1 X1,
  X1 `notin` fv_typ_in_typ T1 ->
  X1 `notin` fv_typ_in_typ (subst_typ_in_typ T1 X1 T2).
Proof.
pose proof subst_typ_in_typ_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_typ_fresh_same : lngen.

(* begin hide *)

Lemma subst_typ_in_binding_fresh_same_mutual :
(forall b1 T1 X1,
  X1 `notin` fv_typ_in_typ T1 ->
  X1 `notin` fv_typ_in_binding (subst_typ_in_binding T1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_binding_fresh_same :
forall b1 T1 X1,
  X1 `notin` fv_typ_in_typ T1 ->
  X1 `notin` fv_typ_in_binding (subst_typ_in_binding T1 X1 b1).
Proof.
pose proof subst_typ_in_binding_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_binding_fresh_same : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_fresh_same_mutual :
(forall e1 T1 X1,
  X1 `notin` fv_typ_in_typ T1 ->
  X1 `notin` fv_typ_in_exp (subst_typ_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_fresh_same :
forall e1 T1 X1,
  X1 `notin` fv_typ_in_typ T1 ->
  X1 `notin` fv_typ_in_exp (subst_typ_in_exp T1 X1 e1).
Proof.
pose proof subst_typ_in_exp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_exp_fresh_same : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_exp_in_exp e1 ->
  x1 `notin` fv_exp_in_exp (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_fresh_same :
forall e2 e1 x1,
  x1 `notin` fv_exp_in_exp e1 ->
  x1 `notin` fv_exp_in_exp (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_fresh_same : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_fresh_mutual :
(forall T2 T1 X1 X2,
  X1 `notin` fv_typ_in_typ T2 ->
  X1 `notin` fv_typ_in_typ T1 ->
  X1 `notin` fv_typ_in_typ (subst_typ_in_typ T1 X2 T2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_fresh :
forall T2 T1 X1 X2,
  X1 `notin` fv_typ_in_typ T2 ->
  X1 `notin` fv_typ_in_typ T1 ->
  X1 `notin` fv_typ_in_typ (subst_typ_in_typ T1 X2 T2).
Proof.
pose proof subst_typ_in_typ_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_typ_fresh : lngen.

(* begin hide *)

Lemma subst_typ_in_binding_fresh_mutual :
(forall b1 T1 X1 X2,
  X1 `notin` fv_typ_in_binding b1 ->
  X1 `notin` fv_typ_in_typ T1 ->
  X1 `notin` fv_typ_in_binding (subst_typ_in_binding T1 X2 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_binding_fresh :
forall b1 T1 X1 X2,
  X1 `notin` fv_typ_in_binding b1 ->
  X1 `notin` fv_typ_in_typ T1 ->
  X1 `notin` fv_typ_in_binding (subst_typ_in_binding T1 X2 b1).
Proof.
pose proof subst_typ_in_binding_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_binding_fresh : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_fresh_mutual :
(forall e1 T1 X1 X2,
  X1 `notin` fv_typ_in_exp e1 ->
  X1 `notin` fv_typ_in_typ T1 ->
  X1 `notin` fv_typ_in_exp (subst_typ_in_exp T1 X2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_fresh :
forall e1 T1 X1 X2,
  X1 `notin` fv_typ_in_exp e1 ->
  X1 `notin` fv_typ_in_typ T1 ->
  X1 `notin` fv_typ_in_exp (subst_typ_in_exp T1 X2 e1).
Proof.
pose proof subst_typ_in_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_exp_fresh : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` fv_exp_in_exp e2 ->
  x1 `notin` fv_exp_in_exp e1 ->
  x1 `notin` fv_exp_in_exp (subst_exp_in_exp e1 x2 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fv_exp_in_exp e2 ->
  x1 `notin` fv_exp_in_exp e1 ->
  x1 `notin` fv_exp_in_exp (subst_exp_in_exp e1 x2 e2).
Proof.
pose proof subst_exp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_fresh : lngen.

Lemma subst_typ_in_typ_lc_typ :
forall T1 T2 X1,
  lc_typ T1 ->
  lc_typ T2 ->
  lc_typ (subst_typ_in_typ T2 X1 T1).
Proof.
default_simp.
Qed.

Hint Resolve subst_typ_in_typ_lc_typ : lngen.

Lemma subst_typ_in_binding_lc_binding :
forall b1 T1 X1,
  lc_binding b1 ->
  lc_typ T1 ->
  lc_binding (subst_typ_in_binding T1 X1 b1).
Proof.
default_simp.
Qed.

Hint Resolve subst_typ_in_binding_lc_binding : lngen.

Lemma subst_typ_in_exp_lc_exp :
forall e1 T1 X1,
  lc_exp e1 ->
  lc_typ T1 ->
  lc_exp (subst_typ_in_exp T1 X1 e1).
Proof.
default_simp.
Qed.

Hint Resolve subst_typ_in_exp_lc_exp : lngen.

Lemma subst_exp_in_exp_lc_exp :
forall e1 e2 x1,
  lc_exp e1 ->
  lc_exp e2 ->
  lc_exp (subst_exp_in_exp e2 x1 e1).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_in_exp_lc_exp : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_open_typ_wrt_typ_rec_mutual :
(forall T3 T1 T2 X1 n1,
  lc_typ T1 ->
  subst_typ_in_typ T1 X1 (open_typ_wrt_typ_rec n1 T2 T3) = open_typ_wrt_typ_rec n1 (subst_typ_in_typ T1 X1 T2) (subst_typ_in_typ T1 X1 T3)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_typ_open_typ_wrt_typ_rec :
forall T3 T1 T2 X1 n1,
  lc_typ T1 ->
  subst_typ_in_typ T1 X1 (open_typ_wrt_typ_rec n1 T2 T3) = open_typ_wrt_typ_rec n1 (subst_typ_in_typ T1 X1 T2) (subst_typ_in_typ T1 X1 T3).
Proof.
pose proof subst_typ_in_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_binding_open_binding_wrt_typ_rec_mutual :
(forall b1 T1 T2 X1 n1,
  lc_typ T1 ->
  subst_typ_in_binding T1 X1 (open_binding_wrt_typ_rec n1 T2 b1) = open_binding_wrt_typ_rec n1 (subst_typ_in_typ T1 X1 T2) (subst_typ_in_binding T1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_binding_open_binding_wrt_typ_rec :
forall b1 T1 T2 X1 n1,
  lc_typ T1 ->
  subst_typ_in_binding T1 X1 (open_binding_wrt_typ_rec n1 T2 b1) = open_binding_wrt_typ_rec n1 (subst_typ_in_typ T1 X1 T2) (subst_typ_in_binding T1 X1 b1).
Proof.
pose proof subst_typ_in_binding_open_binding_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_binding_open_binding_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 T1 T2 X1 n1,
  lc_typ T1 ->
  subst_typ_in_exp T1 X1 (open_exp_wrt_typ_rec n1 T2 e1) = open_exp_wrt_typ_rec n1 (subst_typ_in_typ T1 X1 T2) (subst_typ_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_open_exp_wrt_typ_rec :
forall e1 T1 T2 X1 n1,
  lc_typ T1 ->
  subst_typ_in_exp T1 X1 (open_exp_wrt_typ_rec n1 T2 e1) = open_exp_wrt_typ_rec n1 (subst_typ_in_typ T1 X1 T2) (subst_typ_in_exp T1 X1 e1).
Proof.
pose proof subst_typ_in_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_open_exp_wrt_exp_rec_mutual :
(forall e2 T1 e1 X1 n1,
  subst_typ_in_exp T1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (subst_typ_in_exp T1 X1 e1) (subst_typ_in_exp T1 X1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_open_exp_wrt_exp_rec :
forall e2 T1 e1 X1 n1,
  subst_typ_in_exp T1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (subst_typ_in_exp T1 X1 e1) (subst_typ_in_exp T1 X1 e2).
Proof.
pose proof subst_typ_in_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_typ_rec_mutual :
(forall e2 e1 T1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_typ_rec n1 T1 e2) = open_exp_wrt_typ_rec n1 T1 (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_typ_rec :
forall e2 e1 T1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_typ_rec n1 T1 e2) = open_exp_wrt_typ_rec n1 T1 (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_exp_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_exp_in_exp e1 x1 e2) (subst_exp_in_exp e1 x1 e3)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_exp_rec :
forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_exp_in_exp e1 x1 e2) (subst_exp_in_exp e1 x1 e3).
Proof.
pose proof subst_exp_in_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma subst_typ_in_typ_open_typ_wrt_typ :
forall T3 T1 T2 X1,
  lc_typ T1 ->
  subst_typ_in_typ T1 X1 (open_typ_wrt_typ T3 T2) = open_typ_wrt_typ (subst_typ_in_typ T1 X1 T3) (subst_typ_in_typ T1 X1 T2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_typ_open_typ_wrt_typ : lngen.

Lemma subst_typ_in_binding_open_binding_wrt_typ :
forall b1 T1 T2 X1,
  lc_typ T1 ->
  subst_typ_in_binding T1 X1 (open_binding_wrt_typ b1 T2) = open_binding_wrt_typ (subst_typ_in_binding T1 X1 b1) (subst_typ_in_typ T1 X1 T2).
Proof.
unfold open_binding_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_binding_open_binding_wrt_typ : lngen.

Lemma subst_typ_in_exp_open_exp_wrt_typ :
forall e1 T1 T2 X1,
  lc_typ T1 ->
  subst_typ_in_exp T1 X1 (open_exp_wrt_typ e1 T2) = open_exp_wrt_typ (subst_typ_in_exp T1 X1 e1) (subst_typ_in_typ T1 X1 T2).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_exp_open_exp_wrt_typ : lngen.

Lemma subst_typ_in_exp_open_exp_wrt_exp :
forall e2 T1 e1 X1,
  subst_typ_in_exp T1 X1 (open_exp_wrt_exp e2 e1) = open_exp_wrt_exp (subst_typ_in_exp T1 X1 e2) (subst_typ_in_exp T1 X1 e1).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_typ_in_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_typ :
forall e2 e1 T1 x1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_typ e2 T1) = open_exp_wrt_typ (subst_exp_in_exp e1 x1 e2) T1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_open_exp_wrt_typ : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_exp :
forall e3 e1 e2 x1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp e3 e2) = open_exp_wrt_exp (subst_exp_in_exp e1 x1 e3) (subst_exp_in_exp e1 x1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_open_exp_wrt_exp : lngen.

Lemma subst_typ_in_typ_open_typ_wrt_typ_var :
forall T2 T1 X1 X2,
  X1 <> X2 ->
  lc_typ T1 ->
  open_typ_wrt_typ (subst_typ_in_typ T1 X1 T2) (typ_var_f X2) = subst_typ_in_typ T1 X1 (open_typ_wrt_typ T2 (typ_var_f X2)).
Proof.
intros; rewrite subst_typ_in_typ_open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_typ_open_typ_wrt_typ_var : lngen.

Lemma subst_typ_in_binding_open_binding_wrt_typ_var :
forall b1 T1 X1 X2,
  X1 <> X2 ->
  lc_typ T1 ->
  open_binding_wrt_typ (subst_typ_in_binding T1 X1 b1) (typ_var_f X2) = subst_typ_in_binding T1 X1 (open_binding_wrt_typ b1 (typ_var_f X2)).
Proof.
intros; rewrite subst_typ_in_binding_open_binding_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_binding_open_binding_wrt_typ_var : lngen.

Lemma subst_typ_in_exp_open_exp_wrt_typ_var :
forall e1 T1 X1 X2,
  X1 <> X2 ->
  lc_typ T1 ->
  open_exp_wrt_typ (subst_typ_in_exp T1 X1 e1) (typ_var_f X2) = subst_typ_in_exp T1 X1 (open_exp_wrt_typ e1 (typ_var_f X2)).
Proof.
intros; rewrite subst_typ_in_exp_open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_exp_open_exp_wrt_typ_var : lngen.

Lemma subst_typ_in_exp_open_exp_wrt_exp_var :
forall e1 T1 X1 x1,
  open_exp_wrt_exp (subst_typ_in_exp T1 X1 e1) (exp_var_f x1) = subst_typ_in_exp T1 X1 (open_exp_wrt_exp e1 (exp_var_f x1)).
Proof.
intros; rewrite subst_typ_in_exp_open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_typ_in_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_typ_var :
forall e2 e1 x1 X1,
  lc_exp e1 ->
  open_exp_wrt_typ (subst_exp_in_exp e1 x1 e2) (typ_var_f X1) = subst_exp_in_exp e1 x1 (open_exp_wrt_typ e2 (typ_var_f X1)).
Proof.
intros; rewrite subst_exp_in_exp_open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_open_exp_wrt_typ_var : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_exp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_exp_wrt_exp (subst_exp_in_exp e1 x1 e2) (exp_var_f x2) = subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)).
Proof.
intros; rewrite subst_exp_in_exp_open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_open_exp_wrt_exp_var : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_spec_rec_mutual :
(forall T1 T2 X1 n1,
  subst_typ_in_typ T2 X1 T1 = open_typ_wrt_typ_rec n1 T2 (close_typ_wrt_typ_rec n1 X1 T1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_typ_spec_rec :
forall T1 T2 X1 n1,
  subst_typ_in_typ T2 X1 T1 = open_typ_wrt_typ_rec n1 T2 (close_typ_wrt_typ_rec n1 X1 T1).
Proof.
pose proof subst_typ_in_typ_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_typ_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_binding_spec_rec_mutual :
(forall b1 T1 X1 n1,
  subst_typ_in_binding T1 X1 b1 = open_binding_wrt_typ_rec n1 T1 (close_binding_wrt_typ_rec n1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_binding_spec_rec :
forall b1 T1 X1 n1,
  subst_typ_in_binding T1 X1 b1 = open_binding_wrt_typ_rec n1 T1 (close_binding_wrt_typ_rec n1 X1 b1).
Proof.
pose proof subst_typ_in_binding_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_binding_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_spec_rec_mutual :
(forall e1 T1 X1 n1,
  subst_typ_in_exp T1 X1 e1 = open_exp_wrt_typ_rec n1 T1 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_spec_rec :
forall e1 T1 X1 n1,
  subst_typ_in_exp T1 X1 e1 = open_exp_wrt_typ_rec n1 T1 (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof subst_typ_in_exp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_spec_rec :
forall e1 e2 x1 n1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof subst_exp_in_exp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_spec_rec : lngen.

(* end hide *)

Lemma subst_typ_in_typ_spec :
forall T1 T2 X1,
  subst_typ_in_typ T2 X1 T1 = open_typ_wrt_typ (close_typ_wrt_typ X1 T1) T2.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_typ_spec : lngen.

Lemma subst_typ_in_binding_spec :
forall b1 T1 X1,
  subst_typ_in_binding T1 X1 b1 = open_binding_wrt_typ (close_binding_wrt_typ X1 b1) T1.
Proof.
unfold close_binding_wrt_typ; unfold open_binding_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_binding_spec : lngen.

Lemma subst_typ_in_exp_spec :
forall e1 T1 X1,
  subst_typ_in_exp T1 X1 e1 = open_exp_wrt_typ (close_exp_wrt_typ X1 e1) T1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_exp_spec : lngen.

Lemma subst_exp_in_exp_spec :
forall e1 e2 x1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp (close_exp_wrt_exp x1 e1) e2.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_spec : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_subst_typ_in_typ_mutual :
(forall T1 T2 T3 X2 X1,
  X2 `notin` fv_typ_in_typ T2 ->
  X2 <> X1 ->
  subst_typ_in_typ T2 X1 (subst_typ_in_typ T3 X2 T1) = subst_typ_in_typ (subst_typ_in_typ T2 X1 T3) X2 (subst_typ_in_typ T2 X1 T1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_subst_typ_in_typ :
forall T1 T2 T3 X2 X1,
  X2 `notin` fv_typ_in_typ T2 ->
  X2 <> X1 ->
  subst_typ_in_typ T2 X1 (subst_typ_in_typ T3 X2 T1) = subst_typ_in_typ (subst_typ_in_typ T2 X1 T3) X2 (subst_typ_in_typ T2 X1 T1).
Proof.
pose proof subst_typ_in_typ_subst_typ_in_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_typ_subst_typ_in_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_binding_subst_typ_in_binding_mutual :
(forall b1 T1 T2 X2 X1,
  X2 `notin` fv_typ_in_typ T1 ->
  X2 <> X1 ->
  subst_typ_in_binding T1 X1 (subst_typ_in_binding T2 X2 b1) = subst_typ_in_binding (subst_typ_in_typ T1 X1 T2) X2 (subst_typ_in_binding T1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_binding_subst_typ_in_binding :
forall b1 T1 T2 X2 X1,
  X2 `notin` fv_typ_in_typ T1 ->
  X2 <> X1 ->
  subst_typ_in_binding T1 X1 (subst_typ_in_binding T2 X2 b1) = subst_typ_in_binding (subst_typ_in_typ T1 X1 T2) X2 (subst_typ_in_binding T1 X1 b1).
Proof.
pose proof subst_typ_in_binding_subst_typ_in_binding_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_binding_subst_typ_in_binding : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_subst_typ_in_exp_mutual :
(forall e1 T1 T2 X2 X1,
  X2 `notin` fv_typ_in_typ T1 ->
  X2 <> X1 ->
  subst_typ_in_exp T1 X1 (subst_typ_in_exp T2 X2 e1) = subst_typ_in_exp (subst_typ_in_typ T1 X1 T2) X2 (subst_typ_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_subst_typ_in_exp :
forall e1 T1 T2 X2 X1,
  X2 `notin` fv_typ_in_typ T1 ->
  X2 <> X1 ->
  subst_typ_in_exp T1 X1 (subst_typ_in_exp T2 X2 e1) = subst_typ_in_exp (subst_typ_in_typ T1 X1 T2) X2 (subst_typ_in_exp T1 X1 e1).
Proof.
pose proof subst_typ_in_exp_subst_typ_in_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_exp_subst_typ_in_exp : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_subst_exp_in_exp_mutual :
(forall e1 T1 e2 x1 X1,
  subst_typ_in_exp T1 X1 (subst_exp_in_exp e2 x1 e1) = subst_exp_in_exp (subst_typ_in_exp T1 X1 e2) x1 (subst_typ_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_subst_exp_in_exp :
forall e1 T1 e2 x1 X1,
  subst_typ_in_exp T1 X1 (subst_exp_in_exp e2 x1 e1) = subst_exp_in_exp (subst_typ_in_exp T1 X1 e2) x1 (subst_typ_in_exp T1 X1 e1).
Proof.
pose proof subst_typ_in_exp_subst_exp_in_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_exp_subst_exp_in_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_subst_typ_in_exp_mutual :
(forall e1 e2 T1 X1 x1,
  X1 `notin` fv_typ_in_exp e2 ->
  subst_exp_in_exp e2 x1 (subst_typ_in_exp T1 X1 e1) = subst_typ_in_exp T1 X1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_subst_typ_in_exp :
forall e1 e2 T1 X1 x1,
  X1 `notin` fv_typ_in_exp e2 ->
  subst_exp_in_exp e2 x1 (subst_typ_in_exp T1 X1 e1) = subst_typ_in_exp T1 X1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_subst_typ_in_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_subst_typ_in_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_subst_exp_in_exp_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` fv_exp_in_exp e2 ->
  x2 <> x1 ->
  subst_exp_in_exp e2 x1 (subst_exp_in_exp e3 x2 e1) = subst_exp_in_exp (subst_exp_in_exp e2 x1 e3) x2 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_subst_exp_in_exp :
forall e1 e2 e3 x2 x1,
  x2 `notin` fv_exp_in_exp e2 ->
  x2 <> x1 ->
  subst_exp_in_exp e2 x1 (subst_exp_in_exp e3 x2 e1) = subst_exp_in_exp (subst_exp_in_exp e2 x1 e3) x2 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_subst_exp_in_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_subst_exp_in_exp : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall T2 T1 X1 X2 n1,
  X2 `notin` fv_typ_in_typ T2 ->
  X2 `notin` fv_typ_in_typ T1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 T1 ->
  subst_typ_in_typ T1 X1 T2 = close_typ_wrt_typ_rec n1 X2 (subst_typ_in_typ T1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X2) T2))).
Proof.
apply_mutual_ind typ_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall T2 T1 X1 X2 n1,
  X2 `notin` fv_typ_in_typ T2 ->
  X2 `notin` fv_typ_in_typ T1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 T1 ->
  subst_typ_in_typ T1 X1 T2 = close_typ_wrt_typ_rec n1 X2 (subst_typ_in_typ T1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X2) T2)).
Proof.
pose proof subst_typ_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_binding_close_binding_wrt_typ_rec_open_binding_wrt_typ_rec_mutual :
(forall b1 T1 X1 X2 n1,
  X2 `notin` fv_typ_in_binding b1 ->
  X2 `notin` fv_typ_in_typ T1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 T1 ->
  subst_typ_in_binding T1 X1 b1 = close_binding_wrt_typ_rec n1 X2 (subst_typ_in_binding T1 X1 (open_binding_wrt_typ_rec n1 (typ_var_f X2) b1))).
Proof.
apply_mutual_ind binding_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_binding_close_binding_wrt_typ_rec_open_binding_wrt_typ_rec :
forall b1 T1 X1 X2 n1,
  X2 `notin` fv_typ_in_binding b1 ->
  X2 `notin` fv_typ_in_typ T1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 T1 ->
  subst_typ_in_binding T1 X1 b1 = close_binding_wrt_typ_rec n1 X2 (subst_typ_in_binding T1 X1 (open_binding_wrt_typ_rec n1 (typ_var_f X2) b1)).
Proof.
pose proof subst_typ_in_binding_close_binding_wrt_typ_rec_open_binding_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_binding_close_binding_wrt_typ_rec_open_binding_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e1 T1 X1 X2 n1,
  X2 `notin` fv_typ_in_exp e1 ->
  X2 `notin` fv_typ_in_typ T1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 T1 ->
  subst_typ_in_exp T1 X1 e1 = close_exp_wrt_typ_rec n1 X2 (subst_typ_in_exp T1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X2) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e1 T1 X1 X2 n1,
  X2 `notin` fv_typ_in_exp e1 ->
  X2 `notin` fv_typ_in_typ T1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 T1 ->
  subst_typ_in_exp T1 X1 e1 = close_exp_wrt_typ_rec n1 X2 (subst_typ_in_exp T1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X2) e1)).
Proof.
pose proof subst_typ_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 T1 X1 x1 n1,
  x1 `notin` fv_exp_in_exp e1 ->
  subst_typ_in_exp T1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_typ_in_exp T1 X1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 T1 X1 x1 n1,
  x1 `notin` fv_exp_in_exp e1 ->
  subst_typ_in_exp T1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_typ_in_exp T1 X1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1)).
Proof.
pose proof subst_typ_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e2 e1 x1 X1 n1,
  X1 `notin` fv_typ_in_exp e2 ->
  X1 `notin` fv_typ_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_typ_rec n1 X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e2 e1 x1 X1 n1,
  X1 `notin` fv_typ_in_exp e2 ->
  X1 `notin` fv_typ_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_typ_rec n1 X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e2)).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` fv_exp_in_exp e2 ->
  x2 `notin` fv_exp_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x2) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fv_exp_in_exp e2 ->
  x2 `notin` fv_exp_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x2) e2)).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_open_typ_wrt_typ :
forall T2 T1 X1 X2,
  X2 `notin` fv_typ_in_typ T2 ->
  X2 `notin` fv_typ_in_typ T1 ->
  X2 <> X1 ->
  lc_typ T1 ->
  subst_typ_in_typ T1 X1 T2 = close_typ_wrt_typ X2 (subst_typ_in_typ T1 X1 (open_typ_wrt_typ T2 (typ_var_f X2))).
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_typ_close_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma subst_typ_in_binding_close_binding_wrt_typ_open_binding_wrt_typ :
forall b1 T1 X1 X2,
  X2 `notin` fv_typ_in_binding b1 ->
  X2 `notin` fv_typ_in_typ T1 ->
  X2 <> X1 ->
  lc_typ T1 ->
  subst_typ_in_binding T1 X1 b1 = close_binding_wrt_typ X2 (subst_typ_in_binding T1 X1 (open_binding_wrt_typ b1 (typ_var_f X2))).
Proof.
unfold close_binding_wrt_typ; unfold open_binding_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_binding_close_binding_wrt_typ_open_binding_wrt_typ : lngen.

Lemma subst_typ_in_exp_close_exp_wrt_typ_open_exp_wrt_typ :
forall e1 T1 X1 X2,
  X2 `notin` fv_typ_in_exp e1 ->
  X2 `notin` fv_typ_in_typ T1 ->
  X2 <> X1 ->
  lc_typ T1 ->
  subst_typ_in_exp T1 X1 e1 = close_exp_wrt_typ X2 (subst_typ_in_exp T1 X1 (open_exp_wrt_typ e1 (typ_var_f X2))).
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_exp_close_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma subst_typ_in_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 T1 X1 x1,
  x1 `notin` fv_exp_in_exp e1 ->
  lc_typ T1 ->
  subst_typ_in_exp T1 X1 e1 = close_exp_wrt_exp x1 (subst_typ_in_exp T1 X1 (open_exp_wrt_exp e1 (exp_var_f x1))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_typ_in_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_typ_open_exp_wrt_typ :
forall e2 e1 x1 X1,
  X1 `notin` fv_typ_in_exp e2 ->
  X1 `notin` fv_typ_in_exp e1 ->
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_typ X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_typ e2 (typ_var_f X1))).
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_close_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e2 e1 x1 x2,
  x2 `notin` fv_exp_in_exp e2 ->
  x2 `notin` fv_exp_in_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_typ_in_typ_typ_all :
forall X2 T2 T3 T1 X1,
  lc_typ T1 ->
  X2 `notin` fv_typ_in_typ T1 `union` fv_typ_in_typ T3 `union` singleton X1 ->
  subst_typ_in_typ T1 X1 (typ_all T2 T3) = typ_all (subst_typ_in_typ T1 X1 T2) (close_typ_wrt_typ X2 (subst_typ_in_typ T1 X1 (open_typ_wrt_typ T3 (typ_var_f X2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_typ_in_typ_typ_all : lngen.

Lemma subst_typ_in_exp_exp_abs :
forall x1 T2 e1 T1 X1,
  lc_typ T1 ->
  x1 `notin` fv_exp_in_exp e1 ->
  subst_typ_in_exp T1 X1 (exp_abs T2 e1) = exp_abs (subst_typ_in_typ T1 X1 T2) (close_exp_wrt_exp x1 (subst_typ_in_exp T1 X1 (open_exp_wrt_exp e1 (exp_var_f x1)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_typ_in_exp_exp_abs : lngen.

Lemma subst_typ_in_exp_exp_tabs :
forall X2 T2 e1 T1 X1,
  lc_typ T1 ->
  X2 `notin` fv_typ_in_typ T1 `union` fv_typ_in_exp e1 `union` singleton X1 ->
  subst_typ_in_exp T1 X1 (exp_tabs T2 e1) = exp_tabs (subst_typ_in_typ T1 X1 T2) (close_exp_wrt_typ X2 (subst_typ_in_exp T1 X1 (open_exp_wrt_typ e1 (typ_var_f X2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_typ_in_exp_exp_tabs : lngen.

Lemma subst_typ_in_exp_exp_let :
forall x1 e1 e2 T1 X1,
  lc_typ T1 ->
  x1 `notin` fv_exp_in_exp e2 ->
  subst_typ_in_exp T1 X1 (exp_let e1 e2) = exp_let (subst_typ_in_exp T1 X1 e1) (close_exp_wrt_exp x1 (subst_typ_in_exp T1 X1 (open_exp_wrt_exp e2 (exp_var_f x1)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_typ_in_exp_exp_let : lngen.

Lemma subst_typ_in_exp_exp_case :
forall x1 y1 e1 e2 e3 T1 X1,
  lc_typ T1 ->
  x1 `notin` fv_exp_in_exp e2 ->
  y1 `notin` fv_exp_in_exp e3 ->
  subst_typ_in_exp T1 X1 (exp_case e1 e2 e3) = exp_case (subst_typ_in_exp T1 X1 e1) (close_exp_wrt_exp x1 (subst_typ_in_exp T1 X1 (open_exp_wrt_exp e2 (exp_var_f x1)))) (close_exp_wrt_exp y1 (subst_typ_in_exp T1 X1 (open_exp_wrt_exp e3 (exp_var_f y1)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_typ_in_exp_exp_case : lngen.

Lemma subst_exp_in_exp_exp_abs :
forall x2 T1 e2 e1 x1,
  lc_exp e1 ->
  x2 `notin` fv_exp_in_exp e1 `union` fv_exp_in_exp e2 `union` singleton x1 ->
  subst_exp_in_exp e1 x1 (exp_abs T1 e2) = exp_abs (T1) (close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_in_exp_exp_abs : lngen.

Lemma subst_exp_in_exp_exp_tabs :
forall X1 T1 e2 e1 x1,
  lc_exp e1 ->
  X1 `notin` fv_typ_in_exp e1 `union` fv_typ_in_exp e2 ->
  subst_exp_in_exp e1 x1 (exp_tabs T1 e2) = exp_tabs (T1) (close_exp_wrt_typ X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_typ e2 (typ_var_f X1)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_in_exp_exp_tabs : lngen.

Lemma subst_exp_in_exp_exp_let :
forall x2 e2 e3 e1 x1,
  lc_exp e1 ->
  x2 `notin` fv_exp_in_exp e1 `union` fv_exp_in_exp e3 `union` singleton x1 ->
  subst_exp_in_exp e1 x1 (exp_let e2 e3) = exp_let (subst_exp_in_exp e1 x1 e2) (close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp e3 (exp_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_in_exp_exp_let : lngen.

Lemma subst_exp_in_exp_exp_case :
forall x2 y1 e2 e3 e4 e1 x1,
  lc_exp e1 ->
  x2 `notin` fv_exp_in_exp e1 `union` fv_exp_in_exp e3 `union` singleton x1 ->
  y1 `notin` fv_exp_in_exp e1 `union` fv_exp_in_exp e4 `union` singleton x1 ->
  subst_exp_in_exp e1 x1 (exp_case e2 e3 e4) = exp_case (subst_exp_in_exp e1 x1 e2) (close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp e3 (exp_var_f x2)))) (close_exp_wrt_exp y1 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp e4 (exp_var_f y1)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_in_exp_exp_case : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_intro_rec_mutual :
(forall T1 X1 T2 n1,
  X1 `notin` fv_typ_in_typ T1 ->
  open_typ_wrt_typ_rec n1 T2 T1 = subst_typ_in_typ T2 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) T1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_intro_rec :
forall T1 X1 T2 n1,
  X1 `notin` fv_typ_in_typ T1 ->
  open_typ_wrt_typ_rec n1 T2 T1 = subst_typ_in_typ T2 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) T1).
Proof.
pose proof subst_typ_in_typ_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_typ_intro_rec : lngen.
Hint Rewrite subst_typ_in_typ_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_binding_intro_rec_mutual :
(forall b1 X1 T1 n1,
  X1 `notin` fv_typ_in_binding b1 ->
  open_binding_wrt_typ_rec n1 T1 b1 = subst_typ_in_binding T1 X1 (open_binding_wrt_typ_rec n1 (typ_var_f X1) b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_binding_intro_rec :
forall b1 X1 T1 n1,
  X1 `notin` fv_typ_in_binding b1 ->
  open_binding_wrt_typ_rec n1 T1 b1 = subst_typ_in_binding T1 X1 (open_binding_wrt_typ_rec n1 (typ_var_f X1) b1).
Proof.
pose proof subst_typ_in_binding_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_binding_intro_rec : lngen.
Hint Rewrite subst_typ_in_binding_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_intro_rec_mutual :
(forall e1 X1 T1 n1,
  X1 `notin` fv_typ_in_exp e1 ->
  open_exp_wrt_typ_rec n1 T1 e1 = subst_typ_in_exp T1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_intro_rec :
forall e1 X1 T1 n1,
  X1 `notin` fv_typ_in_exp e1 ->
  open_exp_wrt_typ_rec n1 T1 e1 = subst_typ_in_exp T1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1).
Proof.
pose proof subst_typ_in_exp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_in_exp_intro_rec : lngen.
Hint Rewrite subst_typ_in_exp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` fv_exp_in_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_exp_in_exp e2 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fv_exp_in_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_exp_in_exp e2 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1).
Proof.
pose proof subst_exp_in_exp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_intro_rec : lngen.
Hint Rewrite subst_exp_in_exp_intro_rec using solve [auto] : lngen.

Lemma subst_typ_in_typ_intro :
forall X1 T1 T2,
  X1 `notin` fv_typ_in_typ T1 ->
  open_typ_wrt_typ T1 T2 = subst_typ_in_typ T2 X1 (open_typ_wrt_typ T1 (typ_var_f X1)).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_typ_intro : lngen.

Lemma subst_typ_in_binding_intro :
forall X1 b1 T1,
  X1 `notin` fv_typ_in_binding b1 ->
  open_binding_wrt_typ b1 T1 = subst_typ_in_binding T1 X1 (open_binding_wrt_typ b1 (typ_var_f X1)).
Proof.
unfold open_binding_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_binding_intro : lngen.

Lemma subst_typ_in_exp_intro :
forall X1 e1 T1,
  X1 `notin` fv_typ_in_exp e1 ->
  open_exp_wrt_typ e1 T1 = subst_typ_in_exp T1 X1 (open_exp_wrt_typ e1 (typ_var_f X1)).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

Hint Resolve subst_typ_in_exp_intro : lngen.

Lemma subst_exp_in_exp_intro :
forall x1 e1 e2,
  x1 `notin` fv_exp_in_exp e1 ->
  open_exp_wrt_exp e1 e2 = subst_exp_in_exp e2 x1 (open_exp_wrt_exp e1 (exp_var_f x1)).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
