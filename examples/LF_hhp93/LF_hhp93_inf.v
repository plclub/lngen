Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export LF_hhp93_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme family_ind' := Induction for family Sort Prop
  with object_ind' := Induction for object Sort Prop.

Definition family_object_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  (conj (family_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)
  (object_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)).

Scheme family_rec' := Induction for family Sort Set
  with object_rec' := Induction for object Sort Set.

Definition family_object_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  (pair (family_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)
  (object_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)).

Scheme kind_ind' := Induction for kind Sort Prop.

Definition kind_mutind :=
  fun H1 H2 H3 =>
  kind_ind' H1 H2 H3.

Scheme kind_rec' := Induction for kind Sort Set.

Definition kind_mutrec :=
  fun H1 H2 H3 =>
  kind_rec' H1 H2 H3.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_family_wrt_object_rec (n1 : nat) (x1 : var) (A1 : family) {struct A1} : family :=
  match A1 with
    | family_const a1 => family_const a1
    | family_pi A2 B1 => family_pi (close_family_wrt_object_rec n1 x1 A2) (close_family_wrt_object_rec (S n1) x1 B1)
    | family_abs A2 B1 => family_abs (close_family_wrt_object_rec n1 x1 A2) (close_family_wrt_object_rec (S n1) x1 B1)
    | family_app A2 M1 => family_app (close_family_wrt_object_rec n1 x1 A2) (close_object_wrt_object_rec n1 x1 M1)
  end

with close_object_wrt_object_rec (n1 : nat) (x1 : var) (M1 : object) {struct M1} : object :=
  match M1 with
    | object_const c1 => object_const c1
    | object_var_f x2 => if (x1 == x2) then (object_var_b n1) else (object_var_f x2)
    | object_var_b n2 => if (lt_ge_dec n2 n1) then (object_var_b n2) else (object_var_b (S n2))
    | object_abs A1 M2 => object_abs (close_family_wrt_object_rec n1 x1 A1) (close_object_wrt_object_rec (S n1) x1 M2)
    | object_app M2 N1 => object_app (close_object_wrt_object_rec n1 x1 M2) (close_object_wrt_object_rec n1 x1 N1)
  end.

Definition close_family_wrt_object x1 A1 := close_family_wrt_object_rec 0 x1 A1.

Definition close_object_wrt_object x1 M1 := close_object_wrt_object_rec 0 x1 M1.

Fixpoint close_kind_wrt_object_rec (n1 : nat) (x1 : var) (K1 : kind) {struct K1} : kind :=
  match K1 with
    | kind_type => kind_type
    | kind_pi A1 K2 => kind_pi (close_family_wrt_object_rec n1 x1 A1) (close_kind_wrt_object_rec (S n1) x1 K2)
  end.

Definition close_kind_wrt_object x1 K1 := close_kind_wrt_object_rec 0 x1 K1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_family (A1 : family) {struct A1} : nat :=
  match A1 with
    | family_const a1 => 1
    | family_pi A2 B1 => 1 + (size_family A2) + (size_family B1)
    | family_abs A2 B1 => 1 + (size_family A2) + (size_family B1)
    | family_app A2 M1 => 1 + (size_family A2) + (size_object M1)
  end

with size_object (M1 : object) {struct M1} : nat :=
  match M1 with
    | object_const c1 => 1
    | object_var_f x1 => 1
    | object_var_b n1 => 1
    | object_abs A1 M2 => 1 + (size_family A1) + (size_object M2)
    | object_app M2 N1 => 1 + (size_object M2) + (size_object N1)
  end.

Fixpoint size_kind (K1 : kind) {struct K1} : nat :=
  match K1 with
    | kind_type => 1
    | kind_pi A1 K2 => 1 + (size_family A1) + (size_kind K2)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_family_wrt_object : nat -> family -> Prop :=
  | degree_wrt_object_family_const : forall n1 a1,
    degree_family_wrt_object n1 (family_const a1)
  | degree_wrt_object_family_pi : forall n1 A1 B1,
    degree_family_wrt_object n1 A1 ->
    degree_family_wrt_object (S n1) B1 ->
    degree_family_wrt_object n1 (family_pi A1 B1)
  | degree_wrt_object_family_abs : forall n1 A1 B1,
    degree_family_wrt_object n1 A1 ->
    degree_family_wrt_object (S n1) B1 ->
    degree_family_wrt_object n1 (family_abs A1 B1)
  | degree_wrt_object_family_app : forall n1 A1 M1,
    degree_family_wrt_object n1 A1 ->
    degree_object_wrt_object n1 M1 ->
    degree_family_wrt_object n1 (family_app A1 M1)

with degree_object_wrt_object : nat -> object -> Prop :=
  | degree_wrt_object_object_const : forall n1 c1,
    degree_object_wrt_object n1 (object_const c1)
  | degree_wrt_object_object_var_f : forall n1 x1,
    degree_object_wrt_object n1 (object_var_f x1)
  | degree_wrt_object_object_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_object_wrt_object n1 (object_var_b n2)
  | degree_wrt_object_object_abs : forall n1 A1 M1,
    degree_family_wrt_object n1 A1 ->
    degree_object_wrt_object (S n1) M1 ->
    degree_object_wrt_object n1 (object_abs A1 M1)
  | degree_wrt_object_object_app : forall n1 M1 N1,
    degree_object_wrt_object n1 M1 ->
    degree_object_wrt_object n1 N1 ->
    degree_object_wrt_object n1 (object_app M1 N1).

Scheme degree_family_wrt_object_ind' := Induction for degree_family_wrt_object Sort Prop
  with degree_object_wrt_object_ind' := Induction for degree_object_wrt_object Sort Prop.

Definition degree_family_wrt_object_degree_object_wrt_object_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  (conj (degree_family_wrt_object_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)
  (degree_object_wrt_object_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)).

Hint Constructors degree_family_wrt_object : core lngen.

Hint Constructors degree_object_wrt_object : core lngen.

Inductive degree_kind_wrt_object : nat -> kind -> Prop :=
  | degree_wrt_object_kind_type : forall n1,
    degree_kind_wrt_object n1 (kind_type)
  | degree_wrt_object_kind_pi : forall n1 A1 K1,
    degree_family_wrt_object n1 A1 ->
    degree_kind_wrt_object (S n1) K1 ->
    degree_kind_wrt_object n1 (kind_pi A1 K1).

Scheme degree_kind_wrt_object_ind' := Induction for degree_kind_wrt_object Sort Prop.

Definition degree_kind_wrt_object_mutind :=
  fun H1 H2 H3 =>
  degree_kind_wrt_object_ind' H1 H2 H3.

Hint Constructors degree_kind_wrt_object : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_family : family -> Set :=
  | lc_set_family_const : forall a1,
    lc_set_family (family_const a1)
  | lc_set_family_pi : forall A1 B1,
    lc_set_family A1 ->
    (forall x1 : var, lc_set_family (open_family_wrt_object B1 (object_var_f x1))) ->
    lc_set_family (family_pi A1 B1)
  | lc_set_family_abs : forall A1 B1,
    lc_set_family A1 ->
    (forall x1 : var, lc_set_family (open_family_wrt_object B1 (object_var_f x1))) ->
    lc_set_family (family_abs A1 B1)
  | lc_set_family_app : forall A1 M1,
    lc_set_family A1 ->
    lc_set_object M1 ->
    lc_set_family (family_app A1 M1)

with lc_set_object : object -> Set :=
  | lc_set_object_const : forall c1,
    lc_set_object (object_const c1)
  | lc_set_object_var_f : forall x1,
    lc_set_object (object_var_f x1)
  | lc_set_object_abs : forall A1 M1,
    lc_set_family A1 ->
    (forall x1 : var, lc_set_object (open_object_wrt_object M1 (object_var_f x1))) ->
    lc_set_object (object_abs A1 M1)
  | lc_set_object_app : forall M1 N1,
    lc_set_object M1 ->
    lc_set_object N1 ->
    lc_set_object (object_app M1 N1).

Scheme lc_family_ind' := Induction for lc_family Sort Prop
  with lc_object_ind' := Induction for lc_object Sort Prop.

Definition lc_family_lc_object_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  (conj (lc_family_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)
  (lc_object_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)).

Scheme lc_set_family_ind' := Induction for lc_set_family Sort Prop
  with lc_set_object_ind' := Induction for lc_set_object Sort Prop.

Definition lc_set_family_lc_set_object_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  (conj (lc_set_family_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)
  (lc_set_object_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)).

Scheme lc_set_family_rec' := Induction for lc_set_family Sort Set
  with lc_set_object_rec' := Induction for lc_set_object Sort Set.

Definition lc_set_family_lc_set_object_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  (pair (lc_set_family_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)
  (lc_set_object_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)).

Hint Constructors lc_family : core lngen.

Hint Constructors lc_object : core lngen.

Hint Constructors lc_set_family : core lngen.

Hint Constructors lc_set_object : core lngen.

Inductive lc_set_kind : kind -> Set :=
  | lc_set_kind_type :
    lc_set_kind (kind_type)
  | lc_set_kind_pi : forall A1 K1,
    lc_set_family A1 ->
    (forall x1 : var, lc_set_kind (open_kind_wrt_object K1 (object_var_f x1))) ->
    lc_set_kind (kind_pi A1 K1).

Scheme lc_kind_ind' := Induction for lc_kind Sort Prop.

Definition lc_kind_mutind :=
  fun H1 H2 H3 =>
  lc_kind_ind' H1 H2 H3.

Scheme lc_set_kind_ind' := Induction for lc_set_kind Sort Prop.

Definition lc_set_kind_mutind :=
  fun H1 H2 H3 =>
  lc_set_kind_ind' H1 H2 H3.

Scheme lc_set_kind_rec' := Induction for lc_set_kind Sort Set.

Definition lc_set_kind_mutrec :=
  fun H1 H2 H3 =>
  lc_set_kind_rec' H1 H2 H3.

Hint Constructors lc_kind : core lngen.

Hint Constructors lc_set_kind : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_family_wrt_object A1 := forall x1, lc_family (open_family_wrt_object A1 (object_var_f x1)).

Definition body_object_wrt_object M1 := forall x1, lc_object (open_object_wrt_object M1 (object_var_f x1)).

Hint Unfold body_family_wrt_object : core.

Hint Unfold body_object_wrt_object : core.

Definition body_kind_wrt_object K1 := forall x1, lc_kind (open_kind_wrt_object K1 (object_var_f x1)).

Hint Unfold body_kind_wrt_object : core.


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

Lemma size_family_min_size_object_min_mutual :
(forall A1, 1 <= size_family A1) /\
(forall M1, 1 <= size_object M1).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_family_min :
forall A1, 1 <= size_family A1.
Proof.
pose proof size_family_min_size_object_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_family_min : lngen.

Lemma size_object_min :
forall M1, 1 <= size_object M1.
Proof.
pose proof size_family_min_size_object_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_object_min : lngen.

(* begin hide *)

Lemma size_kind_min_mutual :
(forall K1, 1 <= size_kind K1).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_kind_min :
forall K1, 1 <= size_kind K1.
Proof.
pose proof size_kind_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_kind_min : lngen.

(* begin hide *)

Lemma size_family_close_family_wrt_object_rec_size_object_close_object_wrt_object_rec_mutual :
(forall A1 x1 n1,
  size_family (close_family_wrt_object_rec n1 x1 A1) = size_family A1) /\
(forall M1 x1 n1,
  size_object (close_object_wrt_object_rec n1 x1 M1) = size_object M1).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_family_close_family_wrt_object_rec :
forall A1 x1 n1,
  size_family (close_family_wrt_object_rec n1 x1 A1) = size_family A1.
Proof.
pose proof size_family_close_family_wrt_object_rec_size_object_close_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_family_close_family_wrt_object_rec : lngen.
Hint Rewrite size_family_close_family_wrt_object_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_object_close_object_wrt_object_rec :
forall M1 x1 n1,
  size_object (close_object_wrt_object_rec n1 x1 M1) = size_object M1.
Proof.
pose proof size_family_close_family_wrt_object_rec_size_object_close_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_object_close_object_wrt_object_rec : lngen.
Hint Rewrite size_object_close_object_wrt_object_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_kind_close_kind_wrt_object_rec_mutual :
(forall K1 x1 n1,
  size_kind (close_kind_wrt_object_rec n1 x1 K1) = size_kind K1).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_kind_close_kind_wrt_object_rec :
forall K1 x1 n1,
  size_kind (close_kind_wrt_object_rec n1 x1 K1) = size_kind K1.
Proof.
pose proof size_kind_close_kind_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_kind_close_kind_wrt_object_rec : lngen.
Hint Rewrite size_kind_close_kind_wrt_object_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_family_close_family_wrt_object :
forall A1 x1,
  size_family (close_family_wrt_object x1 A1) = size_family A1.
Proof.
unfold close_family_wrt_object; default_simp.
Qed.

Hint Resolve size_family_close_family_wrt_object : lngen.
Hint Rewrite size_family_close_family_wrt_object using solve [auto] : lngen.

Lemma size_object_close_object_wrt_object :
forall M1 x1,
  size_object (close_object_wrt_object x1 M1) = size_object M1.
Proof.
unfold close_object_wrt_object; default_simp.
Qed.

Hint Resolve size_object_close_object_wrt_object : lngen.
Hint Rewrite size_object_close_object_wrt_object using solve [auto] : lngen.

Lemma size_kind_close_kind_wrt_object :
forall K1 x1,
  size_kind (close_kind_wrt_object x1 K1) = size_kind K1.
Proof.
unfold close_kind_wrt_object; default_simp.
Qed.

Hint Resolve size_kind_close_kind_wrt_object : lngen.
Hint Rewrite size_kind_close_kind_wrt_object using solve [auto] : lngen.

(* begin hide *)

Lemma size_family_open_family_wrt_object_rec_size_object_open_object_wrt_object_rec_mutual :
(forall A1 M1 n1,
  size_family A1 <= size_family (open_family_wrt_object_rec n1 M1 A1)) /\
(forall M1 M2 n1,
  size_object M1 <= size_object (open_object_wrt_object_rec n1 M2 M1)).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_family_open_family_wrt_object_rec :
forall A1 M1 n1,
  size_family A1 <= size_family (open_family_wrt_object_rec n1 M1 A1).
Proof.
pose proof size_family_open_family_wrt_object_rec_size_object_open_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_family_open_family_wrt_object_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_object_open_object_wrt_object_rec :
forall M1 M2 n1,
  size_object M1 <= size_object (open_object_wrt_object_rec n1 M2 M1).
Proof.
pose proof size_family_open_family_wrt_object_rec_size_object_open_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_object_open_object_wrt_object_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_kind_open_kind_wrt_object_rec_mutual :
(forall K1 M1 n1,
  size_kind K1 <= size_kind (open_kind_wrt_object_rec n1 M1 K1)).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_kind_open_kind_wrt_object_rec :
forall K1 M1 n1,
  size_kind K1 <= size_kind (open_kind_wrt_object_rec n1 M1 K1).
Proof.
pose proof size_kind_open_kind_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_kind_open_kind_wrt_object_rec : lngen.

(* end hide *)

Lemma size_family_open_family_wrt_object :
forall A1 M1,
  size_family A1 <= size_family (open_family_wrt_object A1 M1).
Proof.
unfold open_family_wrt_object; default_simp.
Qed.

Hint Resolve size_family_open_family_wrt_object : lngen.

Lemma size_object_open_object_wrt_object :
forall M1 M2,
  size_object M1 <= size_object (open_object_wrt_object M1 M2).
Proof.
unfold open_object_wrt_object; default_simp.
Qed.

Hint Resolve size_object_open_object_wrt_object : lngen.

Lemma size_kind_open_kind_wrt_object :
forall K1 M1,
  size_kind K1 <= size_kind (open_kind_wrt_object K1 M1).
Proof.
unfold open_kind_wrt_object; default_simp.
Qed.

Hint Resolve size_kind_open_kind_wrt_object : lngen.

(* begin hide *)

Lemma size_family_open_family_wrt_object_rec_var_size_object_open_object_wrt_object_rec_var_mutual :
(forall A1 x1 n1,
  size_family (open_family_wrt_object_rec n1 (object_var_f x1) A1) = size_family A1) /\
(forall M1 x1 n1,
  size_object (open_object_wrt_object_rec n1 (object_var_f x1) M1) = size_object M1).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_family_open_family_wrt_object_rec_var :
forall A1 x1 n1,
  size_family (open_family_wrt_object_rec n1 (object_var_f x1) A1) = size_family A1.
Proof.
pose proof size_family_open_family_wrt_object_rec_var_size_object_open_object_wrt_object_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_family_open_family_wrt_object_rec_var : lngen.
Hint Rewrite size_family_open_family_wrt_object_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_object_open_object_wrt_object_rec_var :
forall M1 x1 n1,
  size_object (open_object_wrt_object_rec n1 (object_var_f x1) M1) = size_object M1.
Proof.
pose proof size_family_open_family_wrt_object_rec_var_size_object_open_object_wrt_object_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_object_open_object_wrt_object_rec_var : lngen.
Hint Rewrite size_object_open_object_wrt_object_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_kind_open_kind_wrt_object_rec_var_mutual :
(forall K1 x1 n1,
  size_kind (open_kind_wrt_object_rec n1 (object_var_f x1) K1) = size_kind K1).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_kind_open_kind_wrt_object_rec_var :
forall K1 x1 n1,
  size_kind (open_kind_wrt_object_rec n1 (object_var_f x1) K1) = size_kind K1.
Proof.
pose proof size_kind_open_kind_wrt_object_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_kind_open_kind_wrt_object_rec_var : lngen.
Hint Rewrite size_kind_open_kind_wrt_object_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_family_open_family_wrt_object_var :
forall A1 x1,
  size_family (open_family_wrt_object A1 (object_var_f x1)) = size_family A1.
Proof.
unfold open_family_wrt_object; default_simp.
Qed.

Hint Resolve size_family_open_family_wrt_object_var : lngen.
Hint Rewrite size_family_open_family_wrt_object_var using solve [auto] : lngen.

Lemma size_object_open_object_wrt_object_var :
forall M1 x1,
  size_object (open_object_wrt_object M1 (object_var_f x1)) = size_object M1.
Proof.
unfold open_object_wrt_object; default_simp.
Qed.

Hint Resolve size_object_open_object_wrt_object_var : lngen.
Hint Rewrite size_object_open_object_wrt_object_var using solve [auto] : lngen.

Lemma size_kind_open_kind_wrt_object_var :
forall K1 x1,
  size_kind (open_kind_wrt_object K1 (object_var_f x1)) = size_kind K1.
Proof.
unfold open_kind_wrt_object; default_simp.
Qed.

Hint Resolve size_kind_open_kind_wrt_object_var : lngen.
Hint Rewrite size_kind_open_kind_wrt_object_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_family_wrt_object_S_degree_object_wrt_object_S_mutual :
(forall n1 A1,
  degree_family_wrt_object n1 A1 ->
  degree_family_wrt_object (S n1) A1) /\
(forall n1 M1,
  degree_object_wrt_object n1 M1 ->
  degree_object_wrt_object (S n1) M1).
Proof.
apply_mutual_ind degree_family_wrt_object_degree_object_wrt_object_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_family_wrt_object_S :
forall n1 A1,
  degree_family_wrt_object n1 A1 ->
  degree_family_wrt_object (S n1) A1.
Proof.
pose proof degree_family_wrt_object_S_degree_object_wrt_object_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_family_wrt_object_S : lngen.

Lemma degree_object_wrt_object_S :
forall n1 M1,
  degree_object_wrt_object n1 M1 ->
  degree_object_wrt_object (S n1) M1.
Proof.
pose proof degree_family_wrt_object_S_degree_object_wrt_object_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_object_wrt_object_S : lngen.

(* begin hide *)

Lemma degree_kind_wrt_object_S_mutual :
(forall n1 K1,
  degree_kind_wrt_object n1 K1 ->
  degree_kind_wrt_object (S n1) K1).
Proof.
apply_mutual_ind degree_kind_wrt_object_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_kind_wrt_object_S :
forall n1 K1,
  degree_kind_wrt_object n1 K1 ->
  degree_kind_wrt_object (S n1) K1.
Proof.
pose proof degree_kind_wrt_object_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_kind_wrt_object_S : lngen.

Lemma degree_family_wrt_object_O :
forall n1 A1,
  degree_family_wrt_object O A1 ->
  degree_family_wrt_object n1 A1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_family_wrt_object_O : lngen.

Lemma degree_object_wrt_object_O :
forall n1 M1,
  degree_object_wrt_object O M1 ->
  degree_object_wrt_object n1 M1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_object_wrt_object_O : lngen.

Lemma degree_kind_wrt_object_O :
forall n1 K1,
  degree_kind_wrt_object O K1 ->
  degree_kind_wrt_object n1 K1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_kind_wrt_object_O : lngen.

(* begin hide *)

Lemma degree_family_wrt_object_close_family_wrt_object_rec_degree_object_wrt_object_close_object_wrt_object_rec_mutual :
(forall A1 x1 n1,
  degree_family_wrt_object n1 A1 ->
  degree_family_wrt_object (S n1) (close_family_wrt_object_rec n1 x1 A1)) /\
(forall M1 x1 n1,
  degree_object_wrt_object n1 M1 ->
  degree_object_wrt_object (S n1) (close_object_wrt_object_rec n1 x1 M1)).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_family_wrt_object_close_family_wrt_object_rec :
forall A1 x1 n1,
  degree_family_wrt_object n1 A1 ->
  degree_family_wrt_object (S n1) (close_family_wrt_object_rec n1 x1 A1).
Proof.
pose proof degree_family_wrt_object_close_family_wrt_object_rec_degree_object_wrt_object_close_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_family_wrt_object_close_family_wrt_object_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_object_wrt_object_close_object_wrt_object_rec :
forall M1 x1 n1,
  degree_object_wrt_object n1 M1 ->
  degree_object_wrt_object (S n1) (close_object_wrt_object_rec n1 x1 M1).
Proof.
pose proof degree_family_wrt_object_close_family_wrt_object_rec_degree_object_wrt_object_close_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_object_wrt_object_close_object_wrt_object_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_kind_wrt_object_close_kind_wrt_object_rec_mutual :
(forall K1 x1 n1,
  degree_kind_wrt_object n1 K1 ->
  degree_kind_wrt_object (S n1) (close_kind_wrt_object_rec n1 x1 K1)).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_kind_wrt_object_close_kind_wrt_object_rec :
forall K1 x1 n1,
  degree_kind_wrt_object n1 K1 ->
  degree_kind_wrt_object (S n1) (close_kind_wrt_object_rec n1 x1 K1).
Proof.
pose proof degree_kind_wrt_object_close_kind_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_kind_wrt_object_close_kind_wrt_object_rec : lngen.

(* end hide *)

Lemma degree_family_wrt_object_close_family_wrt_object :
forall A1 x1,
  degree_family_wrt_object 0 A1 ->
  degree_family_wrt_object 1 (close_family_wrt_object x1 A1).
Proof.
unfold close_family_wrt_object; default_simp.
Qed.

Hint Resolve degree_family_wrt_object_close_family_wrt_object : lngen.

Lemma degree_object_wrt_object_close_object_wrt_object :
forall M1 x1,
  degree_object_wrt_object 0 M1 ->
  degree_object_wrt_object 1 (close_object_wrt_object x1 M1).
Proof.
unfold close_object_wrt_object; default_simp.
Qed.

Hint Resolve degree_object_wrt_object_close_object_wrt_object : lngen.

Lemma degree_kind_wrt_object_close_kind_wrt_object :
forall K1 x1,
  degree_kind_wrt_object 0 K1 ->
  degree_kind_wrt_object 1 (close_kind_wrt_object x1 K1).
Proof.
unfold close_kind_wrt_object; default_simp.
Qed.

Hint Resolve degree_kind_wrt_object_close_kind_wrt_object : lngen.

(* begin hide *)

Lemma degree_family_wrt_object_close_family_wrt_object_rec_inv_degree_object_wrt_object_close_object_wrt_object_rec_inv_mutual :
(forall A1 x1 n1,
  degree_family_wrt_object (S n1) (close_family_wrt_object_rec n1 x1 A1) ->
  degree_family_wrt_object n1 A1) /\
(forall M1 x1 n1,
  degree_object_wrt_object (S n1) (close_object_wrt_object_rec n1 x1 M1) ->
  degree_object_wrt_object n1 M1).
Proof.
apply_mutual_ind family_object_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_family_wrt_object_close_family_wrt_object_rec_inv :
forall A1 x1 n1,
  degree_family_wrt_object (S n1) (close_family_wrt_object_rec n1 x1 A1) ->
  degree_family_wrt_object n1 A1.
Proof.
pose proof degree_family_wrt_object_close_family_wrt_object_rec_inv_degree_object_wrt_object_close_object_wrt_object_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_family_wrt_object_close_family_wrt_object_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_object_wrt_object_close_object_wrt_object_rec_inv :
forall M1 x1 n1,
  degree_object_wrt_object (S n1) (close_object_wrt_object_rec n1 x1 M1) ->
  degree_object_wrt_object n1 M1.
Proof.
pose proof degree_family_wrt_object_close_family_wrt_object_rec_inv_degree_object_wrt_object_close_object_wrt_object_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_object_wrt_object_close_object_wrt_object_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_kind_wrt_object_close_kind_wrt_object_rec_inv_mutual :
(forall K1 x1 n1,
  degree_kind_wrt_object (S n1) (close_kind_wrt_object_rec n1 x1 K1) ->
  degree_kind_wrt_object n1 K1).
Proof.
apply_mutual_ind kind_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_kind_wrt_object_close_kind_wrt_object_rec_inv :
forall K1 x1 n1,
  degree_kind_wrt_object (S n1) (close_kind_wrt_object_rec n1 x1 K1) ->
  degree_kind_wrt_object n1 K1.
Proof.
pose proof degree_kind_wrt_object_close_kind_wrt_object_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_kind_wrt_object_close_kind_wrt_object_rec_inv : lngen.

(* end hide *)

Lemma degree_family_wrt_object_close_family_wrt_object_inv :
forall A1 x1,
  degree_family_wrt_object 1 (close_family_wrt_object x1 A1) ->
  degree_family_wrt_object 0 A1.
Proof.
unfold close_family_wrt_object; eauto with lngen.
Qed.

Hint Immediate degree_family_wrt_object_close_family_wrt_object_inv : lngen.

Lemma degree_object_wrt_object_close_object_wrt_object_inv :
forall M1 x1,
  degree_object_wrt_object 1 (close_object_wrt_object x1 M1) ->
  degree_object_wrt_object 0 M1.
Proof.
unfold close_object_wrt_object; eauto with lngen.
Qed.

Hint Immediate degree_object_wrt_object_close_object_wrt_object_inv : lngen.

Lemma degree_kind_wrt_object_close_kind_wrt_object_inv :
forall K1 x1,
  degree_kind_wrt_object 1 (close_kind_wrt_object x1 K1) ->
  degree_kind_wrt_object 0 K1.
Proof.
unfold close_kind_wrt_object; eauto with lngen.
Qed.

Hint Immediate degree_kind_wrt_object_close_kind_wrt_object_inv : lngen.

(* begin hide *)

Lemma degree_family_wrt_object_open_family_wrt_object_rec_degree_object_wrt_object_open_object_wrt_object_rec_mutual :
(forall A1 M1 n1,
  degree_family_wrt_object (S n1) A1 ->
  degree_object_wrt_object n1 M1 ->
  degree_family_wrt_object n1 (open_family_wrt_object_rec n1 M1 A1)) /\
(forall M1 M2 n1,
  degree_object_wrt_object (S n1) M1 ->
  degree_object_wrt_object n1 M2 ->
  degree_object_wrt_object n1 (open_object_wrt_object_rec n1 M2 M1)).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_family_wrt_object_open_family_wrt_object_rec :
forall A1 M1 n1,
  degree_family_wrt_object (S n1) A1 ->
  degree_object_wrt_object n1 M1 ->
  degree_family_wrt_object n1 (open_family_wrt_object_rec n1 M1 A1).
Proof.
pose proof degree_family_wrt_object_open_family_wrt_object_rec_degree_object_wrt_object_open_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_family_wrt_object_open_family_wrt_object_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_object_wrt_object_open_object_wrt_object_rec :
forall M1 M2 n1,
  degree_object_wrt_object (S n1) M1 ->
  degree_object_wrt_object n1 M2 ->
  degree_object_wrt_object n1 (open_object_wrt_object_rec n1 M2 M1).
Proof.
pose proof degree_family_wrt_object_open_family_wrt_object_rec_degree_object_wrt_object_open_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_object_wrt_object_open_object_wrt_object_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_kind_wrt_object_open_kind_wrt_object_rec_mutual :
(forall K1 M1 n1,
  degree_kind_wrt_object (S n1) K1 ->
  degree_object_wrt_object n1 M1 ->
  degree_kind_wrt_object n1 (open_kind_wrt_object_rec n1 M1 K1)).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_kind_wrt_object_open_kind_wrt_object_rec :
forall K1 M1 n1,
  degree_kind_wrt_object (S n1) K1 ->
  degree_object_wrt_object n1 M1 ->
  degree_kind_wrt_object n1 (open_kind_wrt_object_rec n1 M1 K1).
Proof.
pose proof degree_kind_wrt_object_open_kind_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_kind_wrt_object_open_kind_wrt_object_rec : lngen.

(* end hide *)

Lemma degree_family_wrt_object_open_family_wrt_object :
forall A1 M1,
  degree_family_wrt_object 1 A1 ->
  degree_object_wrt_object 0 M1 ->
  degree_family_wrt_object 0 (open_family_wrt_object A1 M1).
Proof.
unfold open_family_wrt_object; default_simp.
Qed.

Hint Resolve degree_family_wrt_object_open_family_wrt_object : lngen.

Lemma degree_object_wrt_object_open_object_wrt_object :
forall M1 M2,
  degree_object_wrt_object 1 M1 ->
  degree_object_wrt_object 0 M2 ->
  degree_object_wrt_object 0 (open_object_wrt_object M1 M2).
Proof.
unfold open_object_wrt_object; default_simp.
Qed.

Hint Resolve degree_object_wrt_object_open_object_wrt_object : lngen.

Lemma degree_kind_wrt_object_open_kind_wrt_object :
forall K1 M1,
  degree_kind_wrt_object 1 K1 ->
  degree_object_wrt_object 0 M1 ->
  degree_kind_wrt_object 0 (open_kind_wrt_object K1 M1).
Proof.
unfold open_kind_wrt_object; default_simp.
Qed.

Hint Resolve degree_kind_wrt_object_open_kind_wrt_object : lngen.

(* begin hide *)

Lemma degree_family_wrt_object_open_family_wrt_object_rec_inv_degree_object_wrt_object_open_object_wrt_object_rec_inv_mutual :
(forall A1 M1 n1,
  degree_family_wrt_object n1 (open_family_wrt_object_rec n1 M1 A1) ->
  degree_family_wrt_object (S n1) A1) /\
(forall M1 M2 n1,
  degree_object_wrt_object n1 (open_object_wrt_object_rec n1 M2 M1) ->
  degree_object_wrt_object (S n1) M1).
Proof.
apply_mutual_ind family_object_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_family_wrt_object_open_family_wrt_object_rec_inv :
forall A1 M1 n1,
  degree_family_wrt_object n1 (open_family_wrt_object_rec n1 M1 A1) ->
  degree_family_wrt_object (S n1) A1.
Proof.
pose proof degree_family_wrt_object_open_family_wrt_object_rec_inv_degree_object_wrt_object_open_object_wrt_object_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_family_wrt_object_open_family_wrt_object_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_object_wrt_object_open_object_wrt_object_rec_inv :
forall M1 M2 n1,
  degree_object_wrt_object n1 (open_object_wrt_object_rec n1 M2 M1) ->
  degree_object_wrt_object (S n1) M1.
Proof.
pose proof degree_family_wrt_object_open_family_wrt_object_rec_inv_degree_object_wrt_object_open_object_wrt_object_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_object_wrt_object_open_object_wrt_object_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_kind_wrt_object_open_kind_wrt_object_rec_inv_mutual :
(forall K1 M1 n1,
  degree_kind_wrt_object n1 (open_kind_wrt_object_rec n1 M1 K1) ->
  degree_kind_wrt_object (S n1) K1).
Proof.
apply_mutual_ind kind_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_kind_wrt_object_open_kind_wrt_object_rec_inv :
forall K1 M1 n1,
  degree_kind_wrt_object n1 (open_kind_wrt_object_rec n1 M1 K1) ->
  degree_kind_wrt_object (S n1) K1.
Proof.
pose proof degree_kind_wrt_object_open_kind_wrt_object_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_kind_wrt_object_open_kind_wrt_object_rec_inv : lngen.

(* end hide *)

Lemma degree_family_wrt_object_open_family_wrt_object_inv :
forall A1 M1,
  degree_family_wrt_object 0 (open_family_wrt_object A1 M1) ->
  degree_family_wrt_object 1 A1.
Proof.
unfold open_family_wrt_object; eauto with lngen.
Qed.

Hint Immediate degree_family_wrt_object_open_family_wrt_object_inv : lngen.

Lemma degree_object_wrt_object_open_object_wrt_object_inv :
forall M1 M2,
  degree_object_wrt_object 0 (open_object_wrt_object M1 M2) ->
  degree_object_wrt_object 1 M1.
Proof.
unfold open_object_wrt_object; eauto with lngen.
Qed.

Hint Immediate degree_object_wrt_object_open_object_wrt_object_inv : lngen.

Lemma degree_kind_wrt_object_open_kind_wrt_object_inv :
forall K1 M1,
  degree_kind_wrt_object 0 (open_kind_wrt_object K1 M1) ->
  degree_kind_wrt_object 1 K1.
Proof.
unfold open_kind_wrt_object; eauto with lngen.
Qed.

Hint Immediate degree_kind_wrt_object_open_kind_wrt_object_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_family_wrt_object_rec_inj_close_object_wrt_object_rec_inj_mutual :
(forall A1 A2 x1 n1,
  close_family_wrt_object_rec n1 x1 A1 = close_family_wrt_object_rec n1 x1 A2 ->
  A1 = A2) /\
(forall M1 M2 x1 n1,
  close_object_wrt_object_rec n1 x1 M1 = close_object_wrt_object_rec n1 x1 M2 ->
  M1 = M2).
Proof.
apply_mutual_ind family_object_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_family_wrt_object_rec_inj :
forall A1 A2 x1 n1,
  close_family_wrt_object_rec n1 x1 A1 = close_family_wrt_object_rec n1 x1 A2 ->
  A1 = A2.
Proof.
pose proof close_family_wrt_object_rec_inj_close_object_wrt_object_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_family_wrt_object_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_object_wrt_object_rec_inj :
forall M1 M2 x1 n1,
  close_object_wrt_object_rec n1 x1 M1 = close_object_wrt_object_rec n1 x1 M2 ->
  M1 = M2.
Proof.
pose proof close_family_wrt_object_rec_inj_close_object_wrt_object_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_object_wrt_object_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_kind_wrt_object_rec_inj_mutual :
(forall K1 K2 x1 n1,
  close_kind_wrt_object_rec n1 x1 K1 = close_kind_wrt_object_rec n1 x1 K2 ->
  K1 = K2).
Proof.
apply_mutual_ind kind_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_kind_wrt_object_rec_inj :
forall K1 K2 x1 n1,
  close_kind_wrt_object_rec n1 x1 K1 = close_kind_wrt_object_rec n1 x1 K2 ->
  K1 = K2.
Proof.
pose proof close_kind_wrt_object_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_kind_wrt_object_rec_inj : lngen.

(* end hide *)

Lemma close_family_wrt_object_inj :
forall A1 A2 x1,
  close_family_wrt_object x1 A1 = close_family_wrt_object x1 A2 ->
  A1 = A2.
Proof.
unfold close_family_wrt_object; eauto with lngen.
Qed.

Hint Immediate close_family_wrt_object_inj : lngen.

Lemma close_object_wrt_object_inj :
forall M1 M2 x1,
  close_object_wrt_object x1 M1 = close_object_wrt_object x1 M2 ->
  M1 = M2.
Proof.
unfold close_object_wrt_object; eauto with lngen.
Qed.

Hint Immediate close_object_wrt_object_inj : lngen.

Lemma close_kind_wrt_object_inj :
forall K1 K2 x1,
  close_kind_wrt_object x1 K1 = close_kind_wrt_object x1 K2 ->
  K1 = K2.
Proof.
unfold close_kind_wrt_object; eauto with lngen.
Qed.

Hint Immediate close_kind_wrt_object_inj : lngen.

(* begin hide *)

Lemma close_family_wrt_object_rec_open_family_wrt_object_rec_close_object_wrt_object_rec_open_object_wrt_object_rec_mutual :
(forall A1 x1 n1,
  x1 `notin` fv_family A1 ->
  close_family_wrt_object_rec n1 x1 (open_family_wrt_object_rec n1 (object_var_f x1) A1) = A1) /\
(forall M1 x1 n1,
  x1 `notin` fv_object M1 ->
  close_object_wrt_object_rec n1 x1 (open_object_wrt_object_rec n1 (object_var_f x1) M1) = M1).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_family_wrt_object_rec_open_family_wrt_object_rec :
forall A1 x1 n1,
  x1 `notin` fv_family A1 ->
  close_family_wrt_object_rec n1 x1 (open_family_wrt_object_rec n1 (object_var_f x1) A1) = A1.
Proof.
pose proof close_family_wrt_object_rec_open_family_wrt_object_rec_close_object_wrt_object_rec_open_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_family_wrt_object_rec_open_family_wrt_object_rec : lngen.
Hint Rewrite close_family_wrt_object_rec_open_family_wrt_object_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_object_wrt_object_rec_open_object_wrt_object_rec :
forall M1 x1 n1,
  x1 `notin` fv_object M1 ->
  close_object_wrt_object_rec n1 x1 (open_object_wrt_object_rec n1 (object_var_f x1) M1) = M1.
Proof.
pose proof close_family_wrt_object_rec_open_family_wrt_object_rec_close_object_wrt_object_rec_open_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_object_wrt_object_rec_open_object_wrt_object_rec : lngen.
Hint Rewrite close_object_wrt_object_rec_open_object_wrt_object_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_kind_wrt_object_rec_open_kind_wrt_object_rec_mutual :
(forall K1 x1 n1,
  x1 `notin` fv_kind K1 ->
  close_kind_wrt_object_rec n1 x1 (open_kind_wrt_object_rec n1 (object_var_f x1) K1) = K1).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_kind_wrt_object_rec_open_kind_wrt_object_rec :
forall K1 x1 n1,
  x1 `notin` fv_kind K1 ->
  close_kind_wrt_object_rec n1 x1 (open_kind_wrt_object_rec n1 (object_var_f x1) K1) = K1.
Proof.
pose proof close_kind_wrt_object_rec_open_kind_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_kind_wrt_object_rec_open_kind_wrt_object_rec : lngen.
Hint Rewrite close_kind_wrt_object_rec_open_kind_wrt_object_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_family_wrt_object_open_family_wrt_object :
forall A1 x1,
  x1 `notin` fv_family A1 ->
  close_family_wrt_object x1 (open_family_wrt_object A1 (object_var_f x1)) = A1.
Proof.
unfold close_family_wrt_object; unfold open_family_wrt_object; default_simp.
Qed.

Hint Resolve close_family_wrt_object_open_family_wrt_object : lngen.
Hint Rewrite close_family_wrt_object_open_family_wrt_object using solve [auto] : lngen.

Lemma close_object_wrt_object_open_object_wrt_object :
forall M1 x1,
  x1 `notin` fv_object M1 ->
  close_object_wrt_object x1 (open_object_wrt_object M1 (object_var_f x1)) = M1.
Proof.
unfold close_object_wrt_object; unfold open_object_wrt_object; default_simp.
Qed.

Hint Resolve close_object_wrt_object_open_object_wrt_object : lngen.
Hint Rewrite close_object_wrt_object_open_object_wrt_object using solve [auto] : lngen.

Lemma close_kind_wrt_object_open_kind_wrt_object :
forall K1 x1,
  x1 `notin` fv_kind K1 ->
  close_kind_wrt_object x1 (open_kind_wrt_object K1 (object_var_f x1)) = K1.
Proof.
unfold close_kind_wrt_object; unfold open_kind_wrt_object; default_simp.
Qed.

Hint Resolve close_kind_wrt_object_open_kind_wrt_object : lngen.
Hint Rewrite close_kind_wrt_object_open_kind_wrt_object using solve [auto] : lngen.

(* begin hide *)

Lemma open_family_wrt_object_rec_close_family_wrt_object_rec_open_object_wrt_object_rec_close_object_wrt_object_rec_mutual :
(forall A1 x1 n1,
  open_family_wrt_object_rec n1 (object_var_f x1) (close_family_wrt_object_rec n1 x1 A1) = A1) /\
(forall M1 x1 n1,
  open_object_wrt_object_rec n1 (object_var_f x1) (close_object_wrt_object_rec n1 x1 M1) = M1).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_family_wrt_object_rec_close_family_wrt_object_rec :
forall A1 x1 n1,
  open_family_wrt_object_rec n1 (object_var_f x1) (close_family_wrt_object_rec n1 x1 A1) = A1.
Proof.
pose proof open_family_wrt_object_rec_close_family_wrt_object_rec_open_object_wrt_object_rec_close_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_family_wrt_object_rec_close_family_wrt_object_rec : lngen.
Hint Rewrite open_family_wrt_object_rec_close_family_wrt_object_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_object_wrt_object_rec_close_object_wrt_object_rec :
forall M1 x1 n1,
  open_object_wrt_object_rec n1 (object_var_f x1) (close_object_wrt_object_rec n1 x1 M1) = M1.
Proof.
pose proof open_family_wrt_object_rec_close_family_wrt_object_rec_open_object_wrt_object_rec_close_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_object_wrt_object_rec_close_object_wrt_object_rec : lngen.
Hint Rewrite open_object_wrt_object_rec_close_object_wrt_object_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_kind_wrt_object_rec_close_kind_wrt_object_rec_mutual :
(forall K1 x1 n1,
  open_kind_wrt_object_rec n1 (object_var_f x1) (close_kind_wrt_object_rec n1 x1 K1) = K1).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_kind_wrt_object_rec_close_kind_wrt_object_rec :
forall K1 x1 n1,
  open_kind_wrt_object_rec n1 (object_var_f x1) (close_kind_wrt_object_rec n1 x1 K1) = K1.
Proof.
pose proof open_kind_wrt_object_rec_close_kind_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_kind_wrt_object_rec_close_kind_wrt_object_rec : lngen.
Hint Rewrite open_kind_wrt_object_rec_close_kind_wrt_object_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_family_wrt_object_close_family_wrt_object :
forall A1 x1,
  open_family_wrt_object (close_family_wrt_object x1 A1) (object_var_f x1) = A1.
Proof.
unfold close_family_wrt_object; unfold open_family_wrt_object; default_simp.
Qed.

Hint Resolve open_family_wrt_object_close_family_wrt_object : lngen.
Hint Rewrite open_family_wrt_object_close_family_wrt_object using solve [auto] : lngen.

Lemma open_object_wrt_object_close_object_wrt_object :
forall M1 x1,
  open_object_wrt_object (close_object_wrt_object x1 M1) (object_var_f x1) = M1.
Proof.
unfold close_object_wrt_object; unfold open_object_wrt_object; default_simp.
Qed.

Hint Resolve open_object_wrt_object_close_object_wrt_object : lngen.
Hint Rewrite open_object_wrt_object_close_object_wrt_object using solve [auto] : lngen.

Lemma open_kind_wrt_object_close_kind_wrt_object :
forall K1 x1,
  open_kind_wrt_object (close_kind_wrt_object x1 K1) (object_var_f x1) = K1.
Proof.
unfold close_kind_wrt_object; unfold open_kind_wrt_object; default_simp.
Qed.

Hint Resolve open_kind_wrt_object_close_kind_wrt_object : lngen.
Hint Rewrite open_kind_wrt_object_close_kind_wrt_object using solve [auto] : lngen.

(* begin hide *)

Lemma open_family_wrt_object_rec_inj_open_object_wrt_object_rec_inj_mutual :
(forall A2 A1 x1 n1,
  x1 `notin` fv_family A2 ->
  x1 `notin` fv_family A1 ->
  open_family_wrt_object_rec n1 (object_var_f x1) A2 = open_family_wrt_object_rec n1 (object_var_f x1) A1 ->
  A2 = A1) /\
(forall M2 M1 x1 n1,
  x1 `notin` fv_object M2 ->
  x1 `notin` fv_object M1 ->
  open_object_wrt_object_rec n1 (object_var_f x1) M2 = open_object_wrt_object_rec n1 (object_var_f x1) M1 ->
  M2 = M1).
Proof.
apply_mutual_ind family_object_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_family_wrt_object_rec_inj :
forall A2 A1 x1 n1,
  x1 `notin` fv_family A2 ->
  x1 `notin` fv_family A1 ->
  open_family_wrt_object_rec n1 (object_var_f x1) A2 = open_family_wrt_object_rec n1 (object_var_f x1) A1 ->
  A2 = A1.
Proof.
pose proof open_family_wrt_object_rec_inj_open_object_wrt_object_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_family_wrt_object_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_object_wrt_object_rec_inj :
forall M2 M1 x1 n1,
  x1 `notin` fv_object M2 ->
  x1 `notin` fv_object M1 ->
  open_object_wrt_object_rec n1 (object_var_f x1) M2 = open_object_wrt_object_rec n1 (object_var_f x1) M1 ->
  M2 = M1.
Proof.
pose proof open_family_wrt_object_rec_inj_open_object_wrt_object_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_object_wrt_object_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_kind_wrt_object_rec_inj_mutual :
(forall K2 K1 x1 n1,
  x1 `notin` fv_kind K2 ->
  x1 `notin` fv_kind K1 ->
  open_kind_wrt_object_rec n1 (object_var_f x1) K2 = open_kind_wrt_object_rec n1 (object_var_f x1) K1 ->
  K2 = K1).
Proof.
apply_mutual_ind kind_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_kind_wrt_object_rec_inj :
forall K2 K1 x1 n1,
  x1 `notin` fv_kind K2 ->
  x1 `notin` fv_kind K1 ->
  open_kind_wrt_object_rec n1 (object_var_f x1) K2 = open_kind_wrt_object_rec n1 (object_var_f x1) K1 ->
  K2 = K1.
Proof.
pose proof open_kind_wrt_object_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_kind_wrt_object_rec_inj : lngen.

(* end hide *)

Lemma open_family_wrt_object_inj :
forall A2 A1 x1,
  x1 `notin` fv_family A2 ->
  x1 `notin` fv_family A1 ->
  open_family_wrt_object A2 (object_var_f x1) = open_family_wrt_object A1 (object_var_f x1) ->
  A2 = A1.
Proof.
unfold open_family_wrt_object; eauto with lngen.
Qed.

Hint Immediate open_family_wrt_object_inj : lngen.

Lemma open_object_wrt_object_inj :
forall M2 M1 x1,
  x1 `notin` fv_object M2 ->
  x1 `notin` fv_object M1 ->
  open_object_wrt_object M2 (object_var_f x1) = open_object_wrt_object M1 (object_var_f x1) ->
  M2 = M1.
Proof.
unfold open_object_wrt_object; eauto with lngen.
Qed.

Hint Immediate open_object_wrt_object_inj : lngen.

Lemma open_kind_wrt_object_inj :
forall K2 K1 x1,
  x1 `notin` fv_kind K2 ->
  x1 `notin` fv_kind K1 ->
  open_kind_wrt_object K2 (object_var_f x1) = open_kind_wrt_object K1 (object_var_f x1) ->
  K2 = K1.
Proof.
unfold open_kind_wrt_object; eauto with lngen.
Qed.

Hint Immediate open_kind_wrt_object_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_family_wrt_object_of_lc_family_degree_object_wrt_object_of_lc_object_mutual :
(forall A1,
  lc_family A1 ->
  degree_family_wrt_object 0 A1) /\
(forall M1,
  lc_object M1 ->
  degree_object_wrt_object 0 M1).
Proof.
apply_mutual_ind lc_family_lc_object_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_family_wrt_object_of_lc_family :
forall A1,
  lc_family A1 ->
  degree_family_wrt_object 0 A1.
Proof.
pose proof degree_family_wrt_object_of_lc_family_degree_object_wrt_object_of_lc_object_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_family_wrt_object_of_lc_family : lngen.

Lemma degree_object_wrt_object_of_lc_object :
forall M1,
  lc_object M1 ->
  degree_object_wrt_object 0 M1.
Proof.
pose proof degree_family_wrt_object_of_lc_family_degree_object_wrt_object_of_lc_object_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_object_wrt_object_of_lc_object : lngen.

(* begin hide *)

Lemma degree_kind_wrt_object_of_lc_kind_mutual :
(forall K1,
  lc_kind K1 ->
  degree_kind_wrt_object 0 K1).
Proof.
apply_mutual_ind lc_kind_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_kind_wrt_object_of_lc_kind :
forall K1,
  lc_kind K1 ->
  degree_kind_wrt_object 0 K1.
Proof.
pose proof degree_kind_wrt_object_of_lc_kind_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_kind_wrt_object_of_lc_kind : lngen.

(* begin hide *)

Lemma lc_family_of_degree_lc_object_of_degree_size_mutual :
forall i1,
(forall A1,
  size_family A1 = i1 ->
  degree_family_wrt_object 0 A1 ->
  lc_family A1) /\
(forall M1,
  size_object M1 = i1 ->
  degree_object_wrt_object 0 M1 ->
  lc_object M1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind family_object_mutind;
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

Lemma lc_family_of_degree :
forall A1,
  degree_family_wrt_object 0 A1 ->
  lc_family A1.
Proof.
intros A1; intros;
pose proof (lc_family_of_degree_lc_object_of_degree_size_mutual (size_family A1));
intuition eauto.
Qed.

Hint Resolve lc_family_of_degree : lngen.

Lemma lc_object_of_degree :
forall M1,
  degree_object_wrt_object 0 M1 ->
  lc_object M1.
Proof.
intros M1; intros;
pose proof (lc_family_of_degree_lc_object_of_degree_size_mutual (size_object M1));
intuition eauto.
Qed.

Hint Resolve lc_object_of_degree : lngen.

(* begin hide *)

Lemma lc_kind_of_degree_size_mutual :
forall i1,
(forall K1,
  size_kind K1 = i1 ->
  degree_kind_wrt_object 0 K1 ->
  lc_kind K1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind kind_mutind;
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

Lemma lc_kind_of_degree :
forall K1,
  degree_kind_wrt_object 0 K1 ->
  lc_kind K1.
Proof.
intros K1; intros;
pose proof (lc_kind_of_degree_size_mutual (size_kind K1));
intuition eauto.
Qed.

Hint Resolve lc_kind_of_degree : lngen.

Ltac family_object_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_family_wrt_object_of_lc_family in J1; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_object_wrt_object_of_lc_object in J1; clear H
          end).

Ltac kind_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_kind_wrt_object_of_lc_kind in J1; clear H
          end).

Lemma lc_family_pi_exists :
forall x1 A1 B1,
  lc_family A1 ->
  lc_family (open_family_wrt_object B1 (object_var_f x1)) ->
  lc_family (family_pi A1 B1).
Proof.
intros; family_object_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_family_abs_exists :
forall x1 A1 B1,
  lc_family A1 ->
  lc_family (open_family_wrt_object B1 (object_var_f x1)) ->
  lc_family (family_abs A1 B1).
Proof.
intros; family_object_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_object_abs_exists :
forall x1 A1 M1,
  lc_family A1 ->
  lc_object (open_object_wrt_object M1 (object_var_f x1)) ->
  lc_object (object_abs A1 M1).
Proof.
intros; family_object_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_kind_pi_exists :
forall x1 A1 K1,
  lc_family A1 ->
  lc_kind (open_kind_wrt_object K1 (object_var_f x1)) ->
  lc_kind (kind_pi A1 K1).
Proof.
intros; kind_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_family (family_pi _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_family_pi_exists x1) : core.

Hint Extern 1 (lc_family (family_abs _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_family_abs_exists x1) : core.

Hint Extern 1 (lc_object (object_abs _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_object_abs_exists x1) : core.

Hint Extern 1 (lc_kind (kind_pi _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_kind_pi_exists x1) : core.

Lemma lc_body_family_wrt_object :
forall A1 M1,
  body_family_wrt_object A1 ->
  lc_object M1 ->
  lc_family (open_family_wrt_object A1 M1).
Proof.
unfold body_family_wrt_object;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
family_object_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_family_wrt_object : lngen.

Lemma lc_body_object_wrt_object :
forall M1 M2,
  body_object_wrt_object M1 ->
  lc_object M2 ->
  lc_object (open_object_wrt_object M1 M2).
Proof.
unfold body_object_wrt_object;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
family_object_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_object_wrt_object : lngen.

Lemma lc_body_kind_wrt_object :
forall K1 M1,
  body_kind_wrt_object K1 ->
  lc_object M1 ->
  lc_kind (open_kind_wrt_object K1 M1).
Proof.
unfold body_kind_wrt_object;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
kind_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_kind_wrt_object : lngen.

Lemma lc_body_family_pi_2 :
forall A1 B1,
  lc_family (family_pi A1 B1) ->
  body_family_wrt_object B1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_family_pi_2 : lngen.

Lemma lc_body_family_abs_2 :
forall A1 B1,
  lc_family (family_abs A1 B1) ->
  body_family_wrt_object B1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_family_abs_2 : lngen.

Lemma lc_body_object_abs_2 :
forall A1 M1,
  lc_object (object_abs A1 M1) ->
  body_object_wrt_object M1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_object_abs_2 : lngen.

Lemma lc_body_kind_pi_2 :
forall A1 K1,
  lc_kind (kind_pi A1 K1) ->
  body_kind_wrt_object K1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_kind_pi_2 : lngen.

(* begin hide *)

Lemma lc_family_unique_lc_object_unique_mutual :
(forall A1 (proof2 proof3 : lc_family A1), proof2 = proof3) /\
(forall M1 (proof2 proof3 : lc_object M1), proof2 = proof3).
Proof.
apply_mutual_ind lc_family_lc_object_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_family_unique :
forall A1 (proof2 proof3 : lc_family A1), proof2 = proof3.
Proof.
pose proof lc_family_unique_lc_object_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_family_unique : lngen.

Lemma lc_object_unique :
forall M1 (proof2 proof3 : lc_object M1), proof2 = proof3.
Proof.
pose proof lc_family_unique_lc_object_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_object_unique : lngen.

(* begin hide *)

Lemma lc_kind_unique_mutual :
(forall K1 (proof2 proof3 : lc_kind K1), proof2 = proof3).
Proof.
apply_mutual_ind lc_kind_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_kind_unique :
forall K1 (proof2 proof3 : lc_kind K1), proof2 = proof3.
Proof.
pose proof lc_kind_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_kind_unique : lngen.

(* begin hide *)

Lemma lc_family_of_lc_set_family_lc_object_of_lc_set_object_mutual :
(forall A1, lc_set_family A1 -> lc_family A1) /\
(forall M1, lc_set_object M1 -> lc_object M1).
Proof.
apply_mutual_ind lc_set_family_lc_set_object_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_family_of_lc_set_family :
forall A1, lc_set_family A1 -> lc_family A1.
Proof.
pose proof lc_family_of_lc_set_family_lc_object_of_lc_set_object_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_family_of_lc_set_family : lngen.

Lemma lc_object_of_lc_set_object :
forall M1, lc_set_object M1 -> lc_object M1.
Proof.
pose proof lc_family_of_lc_set_family_lc_object_of_lc_set_object_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_object_of_lc_set_object : lngen.

(* begin hide *)

Lemma lc_kind_of_lc_set_kind_mutual :
(forall K1, lc_set_kind K1 -> lc_kind K1).
Proof.
apply_mutual_ind lc_set_kind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_kind_of_lc_set_kind :
forall K1, lc_set_kind K1 -> lc_kind K1.
Proof.
pose proof lc_kind_of_lc_set_kind_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_kind_of_lc_set_kind : lngen.

(* begin hide *)

Lemma lc_set_family_of_lc_family_lc_set_object_of_lc_object_size_mutual :
forall i1,
(forall A1,
  size_family A1 = i1 ->
  lc_family A1 ->
  lc_set_family A1) *
(forall M1,
  size_object M1 = i1 ->
  lc_object M1 ->
  lc_set_object M1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind family_object_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_family_of_lc_family
 | apply lc_set_object_of_lc_object
 | apply lc_set_family_of_lc_family
 | apply lc_set_object_of_lc_object];
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

Lemma lc_set_family_of_lc_family :
forall A1,
  lc_family A1 ->
  lc_set_family A1.
Proof.
intros A1; intros;
pose proof (lc_set_family_of_lc_family_lc_set_object_of_lc_object_size_mutual (size_family A1));
intuition eauto.
Qed.

Hint Resolve lc_set_family_of_lc_family : lngen.

Lemma lc_set_object_of_lc_object :
forall M1,
  lc_object M1 ->
  lc_set_object M1.
Proof.
intros M1; intros;
pose proof (lc_set_family_of_lc_family_lc_set_object_of_lc_object_size_mutual (size_object M1));
intuition eauto.
Qed.

Hint Resolve lc_set_object_of_lc_object : lngen.

(* begin hide *)

Lemma lc_set_kind_of_lc_kind_size_mutual :
forall i1,
(forall K1,
  size_kind K1 = i1 ->
  lc_kind K1 ->
  lc_set_kind K1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind kind_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_family_of_lc_family
 | apply lc_set_kind_of_lc_kind
 | apply lc_set_object_of_lc_object];
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

Lemma lc_set_kind_of_lc_kind :
forall K1,
  lc_kind K1 ->
  lc_set_kind K1.
Proof.
intros K1; intros;
pose proof (lc_set_kind_of_lc_kind_size_mutual (size_kind K1));
intuition eauto.
Qed.

Hint Resolve lc_set_kind_of_lc_kind : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_family_wrt_object_rec_degree_family_wrt_object_close_object_wrt_object_rec_degree_object_wrt_object_mutual :
(forall A1 x1 n1,
  degree_family_wrt_object n1 A1 ->
  x1 `notin` fv_family A1 ->
  close_family_wrt_object_rec n1 x1 A1 = A1) /\
(forall M1 x1 n1,
  degree_object_wrt_object n1 M1 ->
  x1 `notin` fv_object M1 ->
  close_object_wrt_object_rec n1 x1 M1 = M1).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_family_wrt_object_rec_degree_family_wrt_object :
forall A1 x1 n1,
  degree_family_wrt_object n1 A1 ->
  x1 `notin` fv_family A1 ->
  close_family_wrt_object_rec n1 x1 A1 = A1.
Proof.
pose proof close_family_wrt_object_rec_degree_family_wrt_object_close_object_wrt_object_rec_degree_object_wrt_object_mutual as H; intuition eauto.
Qed.

Hint Resolve close_family_wrt_object_rec_degree_family_wrt_object : lngen.
Hint Rewrite close_family_wrt_object_rec_degree_family_wrt_object using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_object_wrt_object_rec_degree_object_wrt_object :
forall M1 x1 n1,
  degree_object_wrt_object n1 M1 ->
  x1 `notin` fv_object M1 ->
  close_object_wrt_object_rec n1 x1 M1 = M1.
Proof.
pose proof close_family_wrt_object_rec_degree_family_wrt_object_close_object_wrt_object_rec_degree_object_wrt_object_mutual as H; intuition eauto.
Qed.

Hint Resolve close_object_wrt_object_rec_degree_object_wrt_object : lngen.
Hint Rewrite close_object_wrt_object_rec_degree_object_wrt_object using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_kind_wrt_object_rec_degree_kind_wrt_object_mutual :
(forall K1 x1 n1,
  degree_kind_wrt_object n1 K1 ->
  x1 `notin` fv_kind K1 ->
  close_kind_wrt_object_rec n1 x1 K1 = K1).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_kind_wrt_object_rec_degree_kind_wrt_object :
forall K1 x1 n1,
  degree_kind_wrt_object n1 K1 ->
  x1 `notin` fv_kind K1 ->
  close_kind_wrt_object_rec n1 x1 K1 = K1.
Proof.
pose proof close_kind_wrt_object_rec_degree_kind_wrt_object_mutual as H; intuition eauto.
Qed.

Hint Resolve close_kind_wrt_object_rec_degree_kind_wrt_object : lngen.
Hint Rewrite close_kind_wrt_object_rec_degree_kind_wrt_object using solve [auto] : lngen.

(* end hide *)

Lemma close_family_wrt_object_lc_family :
forall A1 x1,
  lc_family A1 ->
  x1 `notin` fv_family A1 ->
  close_family_wrt_object x1 A1 = A1.
Proof.
unfold close_family_wrt_object; default_simp.
Qed.

Hint Resolve close_family_wrt_object_lc_family : lngen.
Hint Rewrite close_family_wrt_object_lc_family using solve [auto] : lngen.

Lemma close_object_wrt_object_lc_object :
forall M1 x1,
  lc_object M1 ->
  x1 `notin` fv_object M1 ->
  close_object_wrt_object x1 M1 = M1.
Proof.
unfold close_object_wrt_object; default_simp.
Qed.

Hint Resolve close_object_wrt_object_lc_object : lngen.
Hint Rewrite close_object_wrt_object_lc_object using solve [auto] : lngen.

Lemma close_kind_wrt_object_lc_kind :
forall K1 x1,
  lc_kind K1 ->
  x1 `notin` fv_kind K1 ->
  close_kind_wrt_object x1 K1 = K1.
Proof.
unfold close_kind_wrt_object; default_simp.
Qed.

Hint Resolve close_kind_wrt_object_lc_kind : lngen.
Hint Rewrite close_kind_wrt_object_lc_kind using solve [auto] : lngen.

(* begin hide *)

Lemma open_family_wrt_object_rec_degree_family_wrt_object_open_object_wrt_object_rec_degree_object_wrt_object_mutual :
(forall A1 M1 n1,
  degree_family_wrt_object n1 A1 ->
  open_family_wrt_object_rec n1 M1 A1 = A1) /\
(forall M2 M1 n1,
  degree_object_wrt_object n1 M2 ->
  open_object_wrt_object_rec n1 M1 M2 = M2).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_family_wrt_object_rec_degree_family_wrt_object :
forall A1 M1 n1,
  degree_family_wrt_object n1 A1 ->
  open_family_wrt_object_rec n1 M1 A1 = A1.
Proof.
pose proof open_family_wrt_object_rec_degree_family_wrt_object_open_object_wrt_object_rec_degree_object_wrt_object_mutual as H; intuition eauto.
Qed.

Hint Resolve open_family_wrt_object_rec_degree_family_wrt_object : lngen.
Hint Rewrite open_family_wrt_object_rec_degree_family_wrt_object using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_object_wrt_object_rec_degree_object_wrt_object :
forall M2 M1 n1,
  degree_object_wrt_object n1 M2 ->
  open_object_wrt_object_rec n1 M1 M2 = M2.
Proof.
pose proof open_family_wrt_object_rec_degree_family_wrt_object_open_object_wrt_object_rec_degree_object_wrt_object_mutual as H; intuition eauto.
Qed.

Hint Resolve open_object_wrt_object_rec_degree_object_wrt_object : lngen.
Hint Rewrite open_object_wrt_object_rec_degree_object_wrt_object using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_kind_wrt_object_rec_degree_kind_wrt_object_mutual :
(forall K1 M1 n1,
  degree_kind_wrt_object n1 K1 ->
  open_kind_wrt_object_rec n1 M1 K1 = K1).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_kind_wrt_object_rec_degree_kind_wrt_object :
forall K1 M1 n1,
  degree_kind_wrt_object n1 K1 ->
  open_kind_wrt_object_rec n1 M1 K1 = K1.
Proof.
pose proof open_kind_wrt_object_rec_degree_kind_wrt_object_mutual as H; intuition eauto.
Qed.

Hint Resolve open_kind_wrt_object_rec_degree_kind_wrt_object : lngen.
Hint Rewrite open_kind_wrt_object_rec_degree_kind_wrt_object using solve [auto] : lngen.

(* end hide *)

Lemma open_family_wrt_object_lc_family :
forall A1 M1,
  lc_family A1 ->
  open_family_wrt_object A1 M1 = A1.
Proof.
unfold open_family_wrt_object; default_simp.
Qed.

Hint Resolve open_family_wrt_object_lc_family : lngen.
Hint Rewrite open_family_wrt_object_lc_family using solve [auto] : lngen.

Lemma open_object_wrt_object_lc_object :
forall M2 M1,
  lc_object M2 ->
  open_object_wrt_object M2 M1 = M2.
Proof.
unfold open_object_wrt_object; default_simp.
Qed.

Hint Resolve open_object_wrt_object_lc_object : lngen.
Hint Rewrite open_object_wrt_object_lc_object using solve [auto] : lngen.

Lemma open_kind_wrt_object_lc_kind :
forall K1 M1,
  lc_kind K1 ->
  open_kind_wrt_object K1 M1 = K1.
Proof.
unfold open_kind_wrt_object; default_simp.
Qed.

Hint Resolve open_kind_wrt_object_lc_kind : lngen.
Hint Rewrite open_kind_wrt_object_lc_kind using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_family_close_family_wrt_object_rec_fv_object_close_object_wrt_object_rec_mutual :
(forall A1 x1 n1,
  fv_family (close_family_wrt_object_rec n1 x1 A1) [=] remove x1 (fv_family A1)) /\
(forall M1 x1 n1,
  fv_object (close_object_wrt_object_rec n1 x1 M1) [=] remove x1 (fv_object M1)).
Proof.
apply_mutual_ind family_object_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_family_close_family_wrt_object_rec :
forall A1 x1 n1,
  fv_family (close_family_wrt_object_rec n1 x1 A1) [=] remove x1 (fv_family A1).
Proof.
pose proof fv_family_close_family_wrt_object_rec_fv_object_close_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_family_close_family_wrt_object_rec : lngen.
Hint Rewrite fv_family_close_family_wrt_object_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_object_close_object_wrt_object_rec :
forall M1 x1 n1,
  fv_object (close_object_wrt_object_rec n1 x1 M1) [=] remove x1 (fv_object M1).
Proof.
pose proof fv_family_close_family_wrt_object_rec_fv_object_close_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_object_close_object_wrt_object_rec : lngen.
Hint Rewrite fv_object_close_object_wrt_object_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_kind_close_kind_wrt_object_rec_mutual :
(forall K1 x1 n1,
  fv_kind (close_kind_wrt_object_rec n1 x1 K1) [=] remove x1 (fv_kind K1)).
Proof.
apply_mutual_ind kind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_kind_close_kind_wrt_object_rec :
forall K1 x1 n1,
  fv_kind (close_kind_wrt_object_rec n1 x1 K1) [=] remove x1 (fv_kind K1).
Proof.
pose proof fv_kind_close_kind_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_kind_close_kind_wrt_object_rec : lngen.
Hint Rewrite fv_kind_close_kind_wrt_object_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_family_close_family_wrt_object :
forall A1 x1,
  fv_family (close_family_wrt_object x1 A1) [=] remove x1 (fv_family A1).
Proof.
unfold close_family_wrt_object; default_simp.
Qed.

Hint Resolve fv_family_close_family_wrt_object : lngen.
Hint Rewrite fv_family_close_family_wrt_object using solve [auto] : lngen.

Lemma fv_object_close_object_wrt_object :
forall M1 x1,
  fv_object (close_object_wrt_object x1 M1) [=] remove x1 (fv_object M1).
Proof.
unfold close_object_wrt_object; default_simp.
Qed.

Hint Resolve fv_object_close_object_wrt_object : lngen.
Hint Rewrite fv_object_close_object_wrt_object using solve [auto] : lngen.

Lemma fv_kind_close_kind_wrt_object :
forall K1 x1,
  fv_kind (close_kind_wrt_object x1 K1) [=] remove x1 (fv_kind K1).
Proof.
unfold close_kind_wrt_object; default_simp.
Qed.

Hint Resolve fv_kind_close_kind_wrt_object : lngen.
Hint Rewrite fv_kind_close_kind_wrt_object using solve [auto] : lngen.

(* begin hide *)

Lemma fv_family_open_family_wrt_object_rec_lower_fv_object_open_object_wrt_object_rec_lower_mutual :
(forall A1 M1 n1,
  fv_family A1 [<=] fv_family (open_family_wrt_object_rec n1 M1 A1)) /\
(forall M1 M2 n1,
  fv_object M1 [<=] fv_object (open_object_wrt_object_rec n1 M2 M1)).
Proof.
apply_mutual_ind family_object_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_family_open_family_wrt_object_rec_lower :
forall A1 M1 n1,
  fv_family A1 [<=] fv_family (open_family_wrt_object_rec n1 M1 A1).
Proof.
pose proof fv_family_open_family_wrt_object_rec_lower_fv_object_open_object_wrt_object_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_family_open_family_wrt_object_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_object_open_object_wrt_object_rec_lower :
forall M1 M2 n1,
  fv_object M1 [<=] fv_object (open_object_wrt_object_rec n1 M2 M1).
Proof.
pose proof fv_family_open_family_wrt_object_rec_lower_fv_object_open_object_wrt_object_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_object_open_object_wrt_object_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_kind_open_kind_wrt_object_rec_lower_mutual :
(forall K1 M1 n1,
  fv_kind K1 [<=] fv_kind (open_kind_wrt_object_rec n1 M1 K1)).
Proof.
apply_mutual_ind kind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_kind_open_kind_wrt_object_rec_lower :
forall K1 M1 n1,
  fv_kind K1 [<=] fv_kind (open_kind_wrt_object_rec n1 M1 K1).
Proof.
pose proof fv_kind_open_kind_wrt_object_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_kind_open_kind_wrt_object_rec_lower : lngen.

(* end hide *)

Lemma fv_family_open_family_wrt_object_lower :
forall A1 M1,
  fv_family A1 [<=] fv_family (open_family_wrt_object A1 M1).
Proof.
unfold open_family_wrt_object; default_simp.
Qed.

Hint Resolve fv_family_open_family_wrt_object_lower : lngen.

Lemma fv_object_open_object_wrt_object_lower :
forall M1 M2,
  fv_object M1 [<=] fv_object (open_object_wrt_object M1 M2).
Proof.
unfold open_object_wrt_object; default_simp.
Qed.

Hint Resolve fv_object_open_object_wrt_object_lower : lngen.

Lemma fv_kind_open_kind_wrt_object_lower :
forall K1 M1,
  fv_kind K1 [<=] fv_kind (open_kind_wrt_object K1 M1).
Proof.
unfold open_kind_wrt_object; default_simp.
Qed.

Hint Resolve fv_kind_open_kind_wrt_object_lower : lngen.

(* begin hide *)

Lemma fv_family_open_family_wrt_object_rec_upper_fv_object_open_object_wrt_object_rec_upper_mutual :
(forall A1 M1 n1,
  fv_family (open_family_wrt_object_rec n1 M1 A1) [<=] fv_object M1 `union` fv_family A1) /\
(forall M1 M2 n1,
  fv_object (open_object_wrt_object_rec n1 M2 M1) [<=] fv_object M2 `union` fv_object M1).
Proof.
apply_mutual_ind family_object_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_family_open_family_wrt_object_rec_upper :
forall A1 M1 n1,
  fv_family (open_family_wrt_object_rec n1 M1 A1) [<=] fv_object M1 `union` fv_family A1.
Proof.
pose proof fv_family_open_family_wrt_object_rec_upper_fv_object_open_object_wrt_object_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_family_open_family_wrt_object_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_object_open_object_wrt_object_rec_upper :
forall M1 M2 n1,
  fv_object (open_object_wrt_object_rec n1 M2 M1) [<=] fv_object M2 `union` fv_object M1.
Proof.
pose proof fv_family_open_family_wrt_object_rec_upper_fv_object_open_object_wrt_object_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_object_open_object_wrt_object_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_kind_open_kind_wrt_object_rec_upper_mutual :
(forall K1 M1 n1,
  fv_kind (open_kind_wrt_object_rec n1 M1 K1) [<=] fv_object M1 `union` fv_kind K1).
Proof.
apply_mutual_ind kind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_kind_open_kind_wrt_object_rec_upper :
forall K1 M1 n1,
  fv_kind (open_kind_wrt_object_rec n1 M1 K1) [<=] fv_object M1 `union` fv_kind K1.
Proof.
pose proof fv_kind_open_kind_wrt_object_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_kind_open_kind_wrt_object_rec_upper : lngen.

(* end hide *)

Lemma fv_family_open_family_wrt_object_upper :
forall A1 M1,
  fv_family (open_family_wrt_object A1 M1) [<=] fv_object M1 `union` fv_family A1.
Proof.
unfold open_family_wrt_object; default_simp.
Qed.

Hint Resolve fv_family_open_family_wrt_object_upper : lngen.

Lemma fv_object_open_object_wrt_object_upper :
forall M1 M2,
  fv_object (open_object_wrt_object M1 M2) [<=] fv_object M2 `union` fv_object M1.
Proof.
unfold open_object_wrt_object; default_simp.
Qed.

Hint Resolve fv_object_open_object_wrt_object_upper : lngen.

Lemma fv_kind_open_kind_wrt_object_upper :
forall K1 M1,
  fv_kind (open_kind_wrt_object K1 M1) [<=] fv_object M1 `union` fv_kind K1.
Proof.
unfold open_kind_wrt_object; default_simp.
Qed.

Hint Resolve fv_kind_open_kind_wrt_object_upper : lngen.

(* begin hide *)

Lemma fv_family_subst_family_fresh_fv_object_subst_object_fresh_mutual :
(forall A1 M1 x1,
  x1 `notin` fv_family A1 ->
  fv_family (subst_family M1 x1 A1) [=] fv_family A1) /\
(forall M1 M2 x1,
  x1 `notin` fv_object M1 ->
  fv_object (subst_object M2 x1 M1) [=] fv_object M1).
Proof.
apply_mutual_ind family_object_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_family_subst_family_fresh :
forall A1 M1 x1,
  x1 `notin` fv_family A1 ->
  fv_family (subst_family M1 x1 A1) [=] fv_family A1.
Proof.
pose proof fv_family_subst_family_fresh_fv_object_subst_object_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_family_subst_family_fresh : lngen.
Hint Rewrite fv_family_subst_family_fresh using solve [auto] : lngen.

Lemma fv_object_subst_object_fresh :
forall M1 M2 x1,
  x1 `notin` fv_object M1 ->
  fv_object (subst_object M2 x1 M1) [=] fv_object M1.
Proof.
pose proof fv_family_subst_family_fresh_fv_object_subst_object_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_object_subst_object_fresh : lngen.
Hint Rewrite fv_object_subst_object_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_kind_subst_kind_fresh_mutual :
(forall K1 M1 x1,
  x1 `notin` fv_kind K1 ->
  fv_kind (subst_kind M1 x1 K1) [=] fv_kind K1).
Proof.
apply_mutual_ind kind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_kind_subst_kind_fresh :
forall K1 M1 x1,
  x1 `notin` fv_kind K1 ->
  fv_kind (subst_kind M1 x1 K1) [=] fv_kind K1.
Proof.
pose proof fv_kind_subst_kind_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_kind_subst_kind_fresh : lngen.
Hint Rewrite fv_kind_subst_kind_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_family_subst_family_lower_fv_object_subst_object_lower_mutual :
(forall A1 M1 x1,
  remove x1 (fv_family A1) [<=] fv_family (subst_family M1 x1 A1)) /\
(forall M1 M2 x1,
  remove x1 (fv_object M1) [<=] fv_object (subst_object M2 x1 M1)).
Proof.
apply_mutual_ind family_object_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_family_subst_family_lower :
forall A1 M1 x1,
  remove x1 (fv_family A1) [<=] fv_family (subst_family M1 x1 A1).
Proof.
pose proof fv_family_subst_family_lower_fv_object_subst_object_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_family_subst_family_lower : lngen.

Lemma fv_object_subst_object_lower :
forall M1 M2 x1,
  remove x1 (fv_object M1) [<=] fv_object (subst_object M2 x1 M1).
Proof.
pose proof fv_family_subst_family_lower_fv_object_subst_object_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_object_subst_object_lower : lngen.

(* begin hide *)

Lemma fv_kind_subst_kind_lower_mutual :
(forall K1 M1 x1,
  remove x1 (fv_kind K1) [<=] fv_kind (subst_kind M1 x1 K1)).
Proof.
apply_mutual_ind kind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_kind_subst_kind_lower :
forall K1 M1 x1,
  remove x1 (fv_kind K1) [<=] fv_kind (subst_kind M1 x1 K1).
Proof.
pose proof fv_kind_subst_kind_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_kind_subst_kind_lower : lngen.

(* begin hide *)

Lemma fv_family_subst_family_notin_fv_object_subst_object_notin_mutual :
(forall A1 M1 x1 x2,
  x2 `notin` fv_family A1 ->
  x2 `notin` fv_object M1 ->
  x2 `notin` fv_family (subst_family M1 x1 A1)) /\
(forall M1 M2 x1 x2,
  x2 `notin` fv_object M1 ->
  x2 `notin` fv_object M2 ->
  x2 `notin` fv_object (subst_object M2 x1 M1)).
Proof.
apply_mutual_ind family_object_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_family_subst_family_notin :
forall A1 M1 x1 x2,
  x2 `notin` fv_family A1 ->
  x2 `notin` fv_object M1 ->
  x2 `notin` fv_family (subst_family M1 x1 A1).
Proof.
pose proof fv_family_subst_family_notin_fv_object_subst_object_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_family_subst_family_notin : lngen.

Lemma fv_object_subst_object_notin :
forall M1 M2 x1 x2,
  x2 `notin` fv_object M1 ->
  x2 `notin` fv_object M2 ->
  x2 `notin` fv_object (subst_object M2 x1 M1).
Proof.
pose proof fv_family_subst_family_notin_fv_object_subst_object_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_object_subst_object_notin : lngen.

(* begin hide *)

Lemma fv_kind_subst_kind_notin_mutual :
(forall K1 M1 x1 x2,
  x2 `notin` fv_kind K1 ->
  x2 `notin` fv_object M1 ->
  x2 `notin` fv_kind (subst_kind M1 x1 K1)).
Proof.
apply_mutual_ind kind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_kind_subst_kind_notin :
forall K1 M1 x1 x2,
  x2 `notin` fv_kind K1 ->
  x2 `notin` fv_object M1 ->
  x2 `notin` fv_kind (subst_kind M1 x1 K1).
Proof.
pose proof fv_kind_subst_kind_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_kind_subst_kind_notin : lngen.

(* begin hide *)

Lemma fv_family_subst_family_upper_fv_object_subst_object_upper_mutual :
(forall A1 M1 x1,
  fv_family (subst_family M1 x1 A1) [<=] fv_object M1 `union` remove x1 (fv_family A1)) /\
(forall M1 M2 x1,
  fv_object (subst_object M2 x1 M1) [<=] fv_object M2 `union` remove x1 (fv_object M1)).
Proof.
apply_mutual_ind family_object_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_family_subst_family_upper :
forall A1 M1 x1,
  fv_family (subst_family M1 x1 A1) [<=] fv_object M1 `union` remove x1 (fv_family A1).
Proof.
pose proof fv_family_subst_family_upper_fv_object_subst_object_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_family_subst_family_upper : lngen.

Lemma fv_object_subst_object_upper :
forall M1 M2 x1,
  fv_object (subst_object M2 x1 M1) [<=] fv_object M2 `union` remove x1 (fv_object M1).
Proof.
pose proof fv_family_subst_family_upper_fv_object_subst_object_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_object_subst_object_upper : lngen.

(* begin hide *)

Lemma fv_kind_subst_kind_upper_mutual :
(forall K1 M1 x1,
  fv_kind (subst_kind M1 x1 K1) [<=] fv_object M1 `union` remove x1 (fv_kind K1)).
Proof.
apply_mutual_ind kind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_kind_subst_kind_upper :
forall K1 M1 x1,
  fv_kind (subst_kind M1 x1 K1) [<=] fv_object M1 `union` remove x1 (fv_kind K1).
Proof.
pose proof fv_kind_subst_kind_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_kind_subst_kind_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_family_close_family_wrt_object_rec_subst_object_close_object_wrt_object_rec_mutual :
(forall A1 M1 x1 x2 n1,
  degree_object_wrt_object n1 M1 ->
  x1 <> x2 ->
  x2 `notin` fv_object M1 ->
  subst_family M1 x1 (close_family_wrt_object_rec n1 x2 A1) = close_family_wrt_object_rec n1 x2 (subst_family M1 x1 A1)) /\
(forall M2 M1 x1 x2 n1,
  degree_object_wrt_object n1 M1 ->
  x1 <> x2 ->
  x2 `notin` fv_object M1 ->
  subst_object M1 x1 (close_object_wrt_object_rec n1 x2 M2) = close_object_wrt_object_rec n1 x2 (subst_object M1 x1 M2)).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_family_close_family_wrt_object_rec :
forall A1 M1 x1 x2 n1,
  degree_object_wrt_object n1 M1 ->
  x1 <> x2 ->
  x2 `notin` fv_object M1 ->
  subst_family M1 x1 (close_family_wrt_object_rec n1 x2 A1) = close_family_wrt_object_rec n1 x2 (subst_family M1 x1 A1).
Proof.
pose proof subst_family_close_family_wrt_object_rec_subst_object_close_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_family_close_family_wrt_object_rec : lngen.

Lemma subst_object_close_object_wrt_object_rec :
forall M2 M1 x1 x2 n1,
  degree_object_wrt_object n1 M1 ->
  x1 <> x2 ->
  x2 `notin` fv_object M1 ->
  subst_object M1 x1 (close_object_wrt_object_rec n1 x2 M2) = close_object_wrt_object_rec n1 x2 (subst_object M1 x1 M2).
Proof.
pose proof subst_family_close_family_wrt_object_rec_subst_object_close_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_object_close_object_wrt_object_rec : lngen.

(* begin hide *)

Lemma subst_kind_close_kind_wrt_object_rec_mutual :
(forall K1 M1 x1 x2 n1,
  degree_object_wrt_object n1 M1 ->
  x1 <> x2 ->
  x2 `notin` fv_object M1 ->
  subst_kind M1 x1 (close_kind_wrt_object_rec n1 x2 K1) = close_kind_wrt_object_rec n1 x2 (subst_kind M1 x1 K1)).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_kind_close_kind_wrt_object_rec :
forall K1 M1 x1 x2 n1,
  degree_object_wrt_object n1 M1 ->
  x1 <> x2 ->
  x2 `notin` fv_object M1 ->
  subst_kind M1 x1 (close_kind_wrt_object_rec n1 x2 K1) = close_kind_wrt_object_rec n1 x2 (subst_kind M1 x1 K1).
Proof.
pose proof subst_kind_close_kind_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_kind_close_kind_wrt_object_rec : lngen.

Lemma subst_family_close_family_wrt_object :
forall A1 M1 x1 x2,
  lc_object M1 ->  x1 <> x2 ->
  x2 `notin` fv_object M1 ->
  subst_family M1 x1 (close_family_wrt_object x2 A1) = close_family_wrt_object x2 (subst_family M1 x1 A1).
Proof.
unfold close_family_wrt_object; default_simp.
Qed.

Hint Resolve subst_family_close_family_wrt_object : lngen.

Lemma subst_object_close_object_wrt_object :
forall M2 M1 x1 x2,
  lc_object M1 ->  x1 <> x2 ->
  x2 `notin` fv_object M1 ->
  subst_object M1 x1 (close_object_wrt_object x2 M2) = close_object_wrt_object x2 (subst_object M1 x1 M2).
Proof.
unfold close_object_wrt_object; default_simp.
Qed.

Hint Resolve subst_object_close_object_wrt_object : lngen.

Lemma subst_kind_close_kind_wrt_object :
forall K1 M1 x1 x2,
  lc_object M1 ->  x1 <> x2 ->
  x2 `notin` fv_object M1 ->
  subst_kind M1 x1 (close_kind_wrt_object x2 K1) = close_kind_wrt_object x2 (subst_kind M1 x1 K1).
Proof.
unfold close_kind_wrt_object; default_simp.
Qed.

Hint Resolve subst_kind_close_kind_wrt_object : lngen.

(* begin hide *)

Lemma subst_family_degree_family_wrt_object_subst_object_degree_object_wrt_object_mutual :
(forall A1 M1 x1 n1,
  degree_family_wrt_object n1 A1 ->
  degree_object_wrt_object n1 M1 ->
  degree_family_wrt_object n1 (subst_family M1 x1 A1)) /\
(forall M1 M2 x1 n1,
  degree_object_wrt_object n1 M1 ->
  degree_object_wrt_object n1 M2 ->
  degree_object_wrt_object n1 (subst_object M2 x1 M1)).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_family_degree_family_wrt_object :
forall A1 M1 x1 n1,
  degree_family_wrt_object n1 A1 ->
  degree_object_wrt_object n1 M1 ->
  degree_family_wrt_object n1 (subst_family M1 x1 A1).
Proof.
pose proof subst_family_degree_family_wrt_object_subst_object_degree_object_wrt_object_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_family_degree_family_wrt_object : lngen.

Lemma subst_object_degree_object_wrt_object :
forall M1 M2 x1 n1,
  degree_object_wrt_object n1 M1 ->
  degree_object_wrt_object n1 M2 ->
  degree_object_wrt_object n1 (subst_object M2 x1 M1).
Proof.
pose proof subst_family_degree_family_wrt_object_subst_object_degree_object_wrt_object_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_object_degree_object_wrt_object : lngen.

(* begin hide *)

Lemma subst_kind_degree_kind_wrt_object_mutual :
(forall K1 M1 x1 n1,
  degree_kind_wrt_object n1 K1 ->
  degree_object_wrt_object n1 M1 ->
  degree_kind_wrt_object n1 (subst_kind M1 x1 K1)).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_kind_degree_kind_wrt_object :
forall K1 M1 x1 n1,
  degree_kind_wrt_object n1 K1 ->
  degree_object_wrt_object n1 M1 ->
  degree_kind_wrt_object n1 (subst_kind M1 x1 K1).
Proof.
pose proof subst_kind_degree_kind_wrt_object_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_kind_degree_kind_wrt_object : lngen.

(* begin hide *)

Lemma subst_family_fresh_eq_subst_object_fresh_eq_mutual :
(forall A1 M1 x1,
  x1 `notin` fv_family A1 ->
  subst_family M1 x1 A1 = A1) /\
(forall M2 M1 x1,
  x1 `notin` fv_object M2 ->
  subst_object M1 x1 M2 = M2).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_family_fresh_eq :
forall A1 M1 x1,
  x1 `notin` fv_family A1 ->
  subst_family M1 x1 A1 = A1.
Proof.
pose proof subst_family_fresh_eq_subst_object_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_family_fresh_eq : lngen.
Hint Rewrite subst_family_fresh_eq using solve [auto] : lngen.

Lemma subst_object_fresh_eq :
forall M2 M1 x1,
  x1 `notin` fv_object M2 ->
  subst_object M1 x1 M2 = M2.
Proof.
pose proof subst_family_fresh_eq_subst_object_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_object_fresh_eq : lngen.
Hint Rewrite subst_object_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_kind_fresh_eq_mutual :
(forall K1 M1 x1,
  x1 `notin` fv_kind K1 ->
  subst_kind M1 x1 K1 = K1).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_kind_fresh_eq :
forall K1 M1 x1,
  x1 `notin` fv_kind K1 ->
  subst_kind M1 x1 K1 = K1.
Proof.
pose proof subst_kind_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_kind_fresh_eq : lngen.
Hint Rewrite subst_kind_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_family_fresh_same_subst_object_fresh_same_mutual :
(forall A1 M1 x1,
  x1 `notin` fv_object M1 ->
  x1 `notin` fv_family (subst_family M1 x1 A1)) /\
(forall M2 M1 x1,
  x1 `notin` fv_object M1 ->
  x1 `notin` fv_object (subst_object M1 x1 M2)).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_family_fresh_same :
forall A1 M1 x1,
  x1 `notin` fv_object M1 ->
  x1 `notin` fv_family (subst_family M1 x1 A1).
Proof.
pose proof subst_family_fresh_same_subst_object_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_family_fresh_same : lngen.

Lemma subst_object_fresh_same :
forall M2 M1 x1,
  x1 `notin` fv_object M1 ->
  x1 `notin` fv_object (subst_object M1 x1 M2).
Proof.
pose proof subst_family_fresh_same_subst_object_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_object_fresh_same : lngen.

(* begin hide *)

Lemma subst_kind_fresh_same_mutual :
(forall K1 M1 x1,
  x1 `notin` fv_object M1 ->
  x1 `notin` fv_kind (subst_kind M1 x1 K1)).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_kind_fresh_same :
forall K1 M1 x1,
  x1 `notin` fv_object M1 ->
  x1 `notin` fv_kind (subst_kind M1 x1 K1).
Proof.
pose proof subst_kind_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_kind_fresh_same : lngen.

(* begin hide *)

Lemma subst_family_fresh_subst_object_fresh_mutual :
(forall A1 M1 x1 x2,
  x1 `notin` fv_family A1 ->
  x1 `notin` fv_object M1 ->
  x1 `notin` fv_family (subst_family M1 x2 A1)) /\
(forall M2 M1 x1 x2,
  x1 `notin` fv_object M2 ->
  x1 `notin` fv_object M1 ->
  x1 `notin` fv_object (subst_object M1 x2 M2)).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_family_fresh :
forall A1 M1 x1 x2,
  x1 `notin` fv_family A1 ->
  x1 `notin` fv_object M1 ->
  x1 `notin` fv_family (subst_family M1 x2 A1).
Proof.
pose proof subst_family_fresh_subst_object_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_family_fresh : lngen.

Lemma subst_object_fresh :
forall M2 M1 x1 x2,
  x1 `notin` fv_object M2 ->
  x1 `notin` fv_object M1 ->
  x1 `notin` fv_object (subst_object M1 x2 M2).
Proof.
pose proof subst_family_fresh_subst_object_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_object_fresh : lngen.

(* begin hide *)

Lemma subst_kind_fresh_mutual :
(forall K1 M1 x1 x2,
  x1 `notin` fv_kind K1 ->
  x1 `notin` fv_object M1 ->
  x1 `notin` fv_kind (subst_kind M1 x2 K1)).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_kind_fresh :
forall K1 M1 x1 x2,
  x1 `notin` fv_kind K1 ->
  x1 `notin` fv_object M1 ->
  x1 `notin` fv_kind (subst_kind M1 x2 K1).
Proof.
pose proof subst_kind_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_kind_fresh : lngen.

Lemma subst_family_lc_family :
forall A1 M1 x1,
  lc_family A1 ->
  lc_object M1 ->
  lc_family (subst_family M1 x1 A1).
Proof.
default_simp.
Qed.

Hint Resolve subst_family_lc_family : lngen.

Lemma subst_object_lc_object :
forall M1 M2 x1,
  lc_object M1 ->
  lc_object M2 ->
  lc_object (subst_object M2 x1 M1).
Proof.
default_simp.
Qed.

Hint Resolve subst_object_lc_object : lngen.

Lemma subst_kind_lc_kind :
forall K1 M1 x1,
  lc_kind K1 ->
  lc_object M1 ->
  lc_kind (subst_kind M1 x1 K1).
Proof.
default_simp.
Qed.

Hint Resolve subst_kind_lc_kind : lngen.

(* begin hide *)

Lemma subst_family_open_family_wrt_object_rec_subst_object_open_object_wrt_object_rec_mutual :
(forall A1 M1 M2 x1 n1,
  lc_object M1 ->
  subst_family M1 x1 (open_family_wrt_object_rec n1 M2 A1) = open_family_wrt_object_rec n1 (subst_object M1 x1 M2) (subst_family M1 x1 A1)) /\
(forall M3 M1 M2 x1 n1,
  lc_object M1 ->
  subst_object M1 x1 (open_object_wrt_object_rec n1 M2 M3) = open_object_wrt_object_rec n1 (subst_object M1 x1 M2) (subst_object M1 x1 M3)).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_family_open_family_wrt_object_rec :
forall A1 M1 M2 x1 n1,
  lc_object M1 ->
  subst_family M1 x1 (open_family_wrt_object_rec n1 M2 A1) = open_family_wrt_object_rec n1 (subst_object M1 x1 M2) (subst_family M1 x1 A1).
Proof.
pose proof subst_family_open_family_wrt_object_rec_subst_object_open_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_family_open_family_wrt_object_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_object_open_object_wrt_object_rec :
forall M3 M1 M2 x1 n1,
  lc_object M1 ->
  subst_object M1 x1 (open_object_wrt_object_rec n1 M2 M3) = open_object_wrt_object_rec n1 (subst_object M1 x1 M2) (subst_object M1 x1 M3).
Proof.
pose proof subst_family_open_family_wrt_object_rec_subst_object_open_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_object_open_object_wrt_object_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_kind_open_kind_wrt_object_rec_mutual :
(forall K1 M1 M2 x1 n1,
  lc_object M1 ->
  subst_kind M1 x1 (open_kind_wrt_object_rec n1 M2 K1) = open_kind_wrt_object_rec n1 (subst_object M1 x1 M2) (subst_kind M1 x1 K1)).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_kind_open_kind_wrt_object_rec :
forall K1 M1 M2 x1 n1,
  lc_object M1 ->
  subst_kind M1 x1 (open_kind_wrt_object_rec n1 M2 K1) = open_kind_wrt_object_rec n1 (subst_object M1 x1 M2) (subst_kind M1 x1 K1).
Proof.
pose proof subst_kind_open_kind_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_kind_open_kind_wrt_object_rec : lngen.

(* end hide *)

Lemma subst_family_open_family_wrt_object :
forall A1 M1 M2 x1,
  lc_object M1 ->
  subst_family M1 x1 (open_family_wrt_object A1 M2) = open_family_wrt_object (subst_family M1 x1 A1) (subst_object M1 x1 M2).
Proof.
unfold open_family_wrt_object; default_simp.
Qed.

Hint Resolve subst_family_open_family_wrt_object : lngen.

Lemma subst_object_open_object_wrt_object :
forall M3 M1 M2 x1,
  lc_object M1 ->
  subst_object M1 x1 (open_object_wrt_object M3 M2) = open_object_wrt_object (subst_object M1 x1 M3) (subst_object M1 x1 M2).
Proof.
unfold open_object_wrt_object; default_simp.
Qed.

Hint Resolve subst_object_open_object_wrt_object : lngen.

Lemma subst_kind_open_kind_wrt_object :
forall K1 M1 M2 x1,
  lc_object M1 ->
  subst_kind M1 x1 (open_kind_wrt_object K1 M2) = open_kind_wrt_object (subst_kind M1 x1 K1) (subst_object M1 x1 M2).
Proof.
unfold open_kind_wrt_object; default_simp.
Qed.

Hint Resolve subst_kind_open_kind_wrt_object : lngen.

Lemma subst_family_open_family_wrt_object_var :
forall A1 M1 x1 x2,
  x1 <> x2 ->
  lc_object M1 ->
  open_family_wrt_object (subst_family M1 x1 A1) (object_var_f x2) = subst_family M1 x1 (open_family_wrt_object A1 (object_var_f x2)).
Proof.
intros; rewrite subst_family_open_family_wrt_object; default_simp.
Qed.

Hint Resolve subst_family_open_family_wrt_object_var : lngen.

Lemma subst_object_open_object_wrt_object_var :
forall M2 M1 x1 x2,
  x1 <> x2 ->
  lc_object M1 ->
  open_object_wrt_object (subst_object M1 x1 M2) (object_var_f x2) = subst_object M1 x1 (open_object_wrt_object M2 (object_var_f x2)).
Proof.
intros; rewrite subst_object_open_object_wrt_object; default_simp.
Qed.

Hint Resolve subst_object_open_object_wrt_object_var : lngen.

Lemma subst_kind_open_kind_wrt_object_var :
forall K1 M1 x1 x2,
  x1 <> x2 ->
  lc_object M1 ->
  open_kind_wrt_object (subst_kind M1 x1 K1) (object_var_f x2) = subst_kind M1 x1 (open_kind_wrt_object K1 (object_var_f x2)).
Proof.
intros; rewrite subst_kind_open_kind_wrt_object; default_simp.
Qed.

Hint Resolve subst_kind_open_kind_wrt_object_var : lngen.

(* begin hide *)

Lemma subst_family_spec_rec_subst_object_spec_rec_mutual :
(forall A1 M1 x1 n1,
  subst_family M1 x1 A1 = open_family_wrt_object_rec n1 M1 (close_family_wrt_object_rec n1 x1 A1)) /\
(forall M1 M2 x1 n1,
  subst_object M2 x1 M1 = open_object_wrt_object_rec n1 M2 (close_object_wrt_object_rec n1 x1 M1)).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_family_spec_rec :
forall A1 M1 x1 n1,
  subst_family M1 x1 A1 = open_family_wrt_object_rec n1 M1 (close_family_wrt_object_rec n1 x1 A1).
Proof.
pose proof subst_family_spec_rec_subst_object_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_family_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_object_spec_rec :
forall M1 M2 x1 n1,
  subst_object M2 x1 M1 = open_object_wrt_object_rec n1 M2 (close_object_wrt_object_rec n1 x1 M1).
Proof.
pose proof subst_family_spec_rec_subst_object_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_object_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_kind_spec_rec_mutual :
(forall K1 M1 x1 n1,
  subst_kind M1 x1 K1 = open_kind_wrt_object_rec n1 M1 (close_kind_wrt_object_rec n1 x1 K1)).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_kind_spec_rec :
forall K1 M1 x1 n1,
  subst_kind M1 x1 K1 = open_kind_wrt_object_rec n1 M1 (close_kind_wrt_object_rec n1 x1 K1).
Proof.
pose proof subst_kind_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_kind_spec_rec : lngen.

(* end hide *)

Lemma subst_family_spec :
forall A1 M1 x1,
  subst_family M1 x1 A1 = open_family_wrt_object (close_family_wrt_object x1 A1) M1.
Proof.
unfold close_family_wrt_object; unfold open_family_wrt_object; default_simp.
Qed.

Hint Resolve subst_family_spec : lngen.

Lemma subst_object_spec :
forall M1 M2 x1,
  subst_object M2 x1 M1 = open_object_wrt_object (close_object_wrt_object x1 M1) M2.
Proof.
unfold close_object_wrt_object; unfold open_object_wrt_object; default_simp.
Qed.

Hint Resolve subst_object_spec : lngen.

Lemma subst_kind_spec :
forall K1 M1 x1,
  subst_kind M1 x1 K1 = open_kind_wrt_object (close_kind_wrt_object x1 K1) M1.
Proof.
unfold close_kind_wrt_object; unfold open_kind_wrt_object; default_simp.
Qed.

Hint Resolve subst_kind_spec : lngen.

(* begin hide *)

Lemma subst_family_subst_family_subst_object_subst_object_mutual :
(forall A1 M1 M2 x2 x1,
  x2 `notin` fv_object M1 ->
  x2 <> x1 ->
  subst_family M1 x1 (subst_family M2 x2 A1) = subst_family (subst_object M1 x1 M2) x2 (subst_family M1 x1 A1)) /\
(forall M1 M2 M3 x2 x1,
  x2 `notin` fv_object M2 ->
  x2 <> x1 ->
  subst_object M2 x1 (subst_object M3 x2 M1) = subst_object (subst_object M2 x1 M3) x2 (subst_object M2 x1 M1)).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_family_subst_family :
forall A1 M1 M2 x2 x1,
  x2 `notin` fv_object M1 ->
  x2 <> x1 ->
  subst_family M1 x1 (subst_family M2 x2 A1) = subst_family (subst_object M1 x1 M2) x2 (subst_family M1 x1 A1).
Proof.
pose proof subst_family_subst_family_subst_object_subst_object_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_family_subst_family : lngen.

Lemma subst_object_subst_object :
forall M1 M2 M3 x2 x1,
  x2 `notin` fv_object M2 ->
  x2 <> x1 ->
  subst_object M2 x1 (subst_object M3 x2 M1) = subst_object (subst_object M2 x1 M3) x2 (subst_object M2 x1 M1).
Proof.
pose proof subst_family_subst_family_subst_object_subst_object_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_object_subst_object : lngen.

(* begin hide *)

Lemma subst_kind_subst_kind_mutual :
(forall K1 M1 M2 x2 x1,
  x2 `notin` fv_object M1 ->
  x2 <> x1 ->
  subst_kind M1 x1 (subst_kind M2 x2 K1) = subst_kind (subst_object M1 x1 M2) x2 (subst_kind M1 x1 K1)).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_kind_subst_kind :
forall K1 M1 M2 x2 x1,
  x2 `notin` fv_object M1 ->
  x2 <> x1 ->
  subst_kind M1 x1 (subst_kind M2 x2 K1) = subst_kind (subst_object M1 x1 M2) x2 (subst_kind M1 x1 K1).
Proof.
pose proof subst_kind_subst_kind_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_kind_subst_kind : lngen.

(* begin hide *)

Lemma subst_family_close_family_wrt_object_rec_open_family_wrt_object_rec_subst_object_close_object_wrt_object_rec_open_object_wrt_object_rec_mutual :
(forall A1 M1 x1 x2 n1,
  x2 `notin` fv_family A1 ->
  x2 `notin` fv_object M1 ->
  x2 <> x1 ->
  degree_object_wrt_object n1 M1 ->
  subst_family M1 x1 A1 = close_family_wrt_object_rec n1 x2 (subst_family M1 x1 (open_family_wrt_object_rec n1 (object_var_f x2) A1))) *
(forall M2 M1 x1 x2 n1,
  x2 `notin` fv_object M2 ->
  x2 `notin` fv_object M1 ->
  x2 <> x1 ->
  degree_object_wrt_object n1 M1 ->
  subst_object M1 x1 M2 = close_object_wrt_object_rec n1 x2 (subst_object M1 x1 (open_object_wrt_object_rec n1 (object_var_f x2) M2))).
Proof.
apply_mutual_ind family_object_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_family_close_family_wrt_object_rec_open_family_wrt_object_rec :
forall A1 M1 x1 x2 n1,
  x2 `notin` fv_family A1 ->
  x2 `notin` fv_object M1 ->
  x2 <> x1 ->
  degree_object_wrt_object n1 M1 ->
  subst_family M1 x1 A1 = close_family_wrt_object_rec n1 x2 (subst_family M1 x1 (open_family_wrt_object_rec n1 (object_var_f x2) A1)).
Proof.
pose proof subst_family_close_family_wrt_object_rec_open_family_wrt_object_rec_subst_object_close_object_wrt_object_rec_open_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_family_close_family_wrt_object_rec_open_family_wrt_object_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_object_close_object_wrt_object_rec_open_object_wrt_object_rec :
forall M2 M1 x1 x2 n1,
  x2 `notin` fv_object M2 ->
  x2 `notin` fv_object M1 ->
  x2 <> x1 ->
  degree_object_wrt_object n1 M1 ->
  subst_object M1 x1 M2 = close_object_wrt_object_rec n1 x2 (subst_object M1 x1 (open_object_wrt_object_rec n1 (object_var_f x2) M2)).
Proof.
pose proof subst_family_close_family_wrt_object_rec_open_family_wrt_object_rec_subst_object_close_object_wrt_object_rec_open_object_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_object_close_object_wrt_object_rec_open_object_wrt_object_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_kind_close_kind_wrt_object_rec_open_kind_wrt_object_rec_mutual :
(forall K1 M1 x1 x2 n1,
  x2 `notin` fv_kind K1 ->
  x2 `notin` fv_object M1 ->
  x2 <> x1 ->
  degree_object_wrt_object n1 M1 ->
  subst_kind M1 x1 K1 = close_kind_wrt_object_rec n1 x2 (subst_kind M1 x1 (open_kind_wrt_object_rec n1 (object_var_f x2) K1))).
Proof.
apply_mutual_ind kind_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_kind_close_kind_wrt_object_rec_open_kind_wrt_object_rec :
forall K1 M1 x1 x2 n1,
  x2 `notin` fv_kind K1 ->
  x2 `notin` fv_object M1 ->
  x2 <> x1 ->
  degree_object_wrt_object n1 M1 ->
  subst_kind M1 x1 K1 = close_kind_wrt_object_rec n1 x2 (subst_kind M1 x1 (open_kind_wrt_object_rec n1 (object_var_f x2) K1)).
Proof.
pose proof subst_kind_close_kind_wrt_object_rec_open_kind_wrt_object_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_kind_close_kind_wrt_object_rec_open_kind_wrt_object_rec : lngen.

(* end hide *)

Lemma subst_family_close_family_wrt_object_open_family_wrt_object :
forall A1 M1 x1 x2,
  x2 `notin` fv_family A1 ->
  x2 `notin` fv_object M1 ->
  x2 <> x1 ->
  lc_object M1 ->
  subst_family M1 x1 A1 = close_family_wrt_object x2 (subst_family M1 x1 (open_family_wrt_object A1 (object_var_f x2))).
Proof.
unfold close_family_wrt_object; unfold open_family_wrt_object; default_simp.
Qed.

Hint Resolve subst_family_close_family_wrt_object_open_family_wrt_object : lngen.

Lemma subst_object_close_object_wrt_object_open_object_wrt_object :
forall M2 M1 x1 x2,
  x2 `notin` fv_object M2 ->
  x2 `notin` fv_object M1 ->
  x2 <> x1 ->
  lc_object M1 ->
  subst_object M1 x1 M2 = close_object_wrt_object x2 (subst_object M1 x1 (open_object_wrt_object M2 (object_var_f x2))).
Proof.
unfold close_object_wrt_object; unfold open_object_wrt_object; default_simp.
Qed.

Hint Resolve subst_object_close_object_wrt_object_open_object_wrt_object : lngen.

Lemma subst_kind_close_kind_wrt_object_open_kind_wrt_object :
forall K1 M1 x1 x2,
  x2 `notin` fv_kind K1 ->
  x2 `notin` fv_object M1 ->
  x2 <> x1 ->
  lc_object M1 ->
  subst_kind M1 x1 K1 = close_kind_wrt_object x2 (subst_kind M1 x1 (open_kind_wrt_object K1 (object_var_f x2))).
Proof.
unfold close_kind_wrt_object; unfold open_kind_wrt_object; default_simp.
Qed.

Hint Resolve subst_kind_close_kind_wrt_object_open_kind_wrt_object : lngen.

Lemma subst_family_family_pi :
forall x2 A1 B1 M1 x1,
  lc_object M1 ->
  x2 `notin` fv_object M1 `union` fv_family B1 `union` singleton x1 ->
  subst_family M1 x1 (family_pi A1 B1) = family_pi (subst_family M1 x1 A1) (close_family_wrt_object x2 (subst_family M1 x1 (open_family_wrt_object B1 (object_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_family_family_pi : lngen.

Lemma subst_family_family_abs :
forall x2 A1 B1 M1 x1,
  lc_object M1 ->
  x2 `notin` fv_object M1 `union` fv_family B1 `union` singleton x1 ->
  subst_family M1 x1 (family_abs A1 B1) = family_abs (subst_family M1 x1 A1) (close_family_wrt_object x2 (subst_family M1 x1 (open_family_wrt_object B1 (object_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_family_family_abs : lngen.

Lemma subst_object_object_abs :
forall x2 A1 M2 M1 x1,
  lc_object M1 ->
  x2 `notin` fv_object M1 `union` fv_object M2 `union` singleton x1 ->
  subst_object M1 x1 (object_abs A1 M2) = object_abs (subst_family M1 x1 A1) (close_object_wrt_object x2 (subst_object M1 x1 (open_object_wrt_object M2 (object_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_object_object_abs : lngen.

Lemma subst_kind_kind_pi :
forall x2 A1 K1 M1 x1,
  lc_object M1 ->
  x2 `notin` fv_object M1 `union` fv_kind K1 `union` singleton x1 ->
  subst_kind M1 x1 (kind_pi A1 K1) = kind_pi (subst_family M1 x1 A1) (close_kind_wrt_object x2 (subst_kind M1 x1 (open_kind_wrt_object K1 (object_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_kind_kind_pi : lngen.

(* begin hide *)

Lemma subst_family_intro_rec_subst_object_intro_rec_mutual :
(forall A1 x1 M1 n1,
  x1 `notin` fv_family A1 ->
  open_family_wrt_object_rec n1 M1 A1 = subst_family M1 x1 (open_family_wrt_object_rec n1 (object_var_f x1) A1)) /\
(forall M1 x1 M2 n1,
  x1 `notin` fv_object M1 ->
  open_object_wrt_object_rec n1 M2 M1 = subst_object M2 x1 (open_object_wrt_object_rec n1 (object_var_f x1) M1)).
Proof.
apply_mutual_ind family_object_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_family_intro_rec :
forall A1 x1 M1 n1,
  x1 `notin` fv_family A1 ->
  open_family_wrt_object_rec n1 M1 A1 = subst_family M1 x1 (open_family_wrt_object_rec n1 (object_var_f x1) A1).
Proof.
pose proof subst_family_intro_rec_subst_object_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_family_intro_rec : lngen.
Hint Rewrite subst_family_intro_rec using solve [auto] : lngen.

Lemma subst_object_intro_rec :
forall M1 x1 M2 n1,
  x1 `notin` fv_object M1 ->
  open_object_wrt_object_rec n1 M2 M1 = subst_object M2 x1 (open_object_wrt_object_rec n1 (object_var_f x1) M1).
Proof.
pose proof subst_family_intro_rec_subst_object_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_object_intro_rec : lngen.
Hint Rewrite subst_object_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_kind_intro_rec_mutual :
(forall K1 x1 M1 n1,
  x1 `notin` fv_kind K1 ->
  open_kind_wrt_object_rec n1 M1 K1 = subst_kind M1 x1 (open_kind_wrt_object_rec n1 (object_var_f x1) K1)).
Proof.
apply_mutual_ind kind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_kind_intro_rec :
forall K1 x1 M1 n1,
  x1 `notin` fv_kind K1 ->
  open_kind_wrt_object_rec n1 M1 K1 = subst_kind M1 x1 (open_kind_wrt_object_rec n1 (object_var_f x1) K1).
Proof.
pose proof subst_kind_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_kind_intro_rec : lngen.
Hint Rewrite subst_kind_intro_rec using solve [auto] : lngen.

Lemma subst_family_intro :
forall x1 A1 M1,
  x1 `notin` fv_family A1 ->
  open_family_wrt_object A1 M1 = subst_family M1 x1 (open_family_wrt_object A1 (object_var_f x1)).
Proof.
unfold open_family_wrt_object; default_simp.
Qed.

Hint Resolve subst_family_intro : lngen.

Lemma subst_object_intro :
forall x1 M1 M2,
  x1 `notin` fv_object M1 ->
  open_object_wrt_object M1 M2 = subst_object M2 x1 (open_object_wrt_object M1 (object_var_f x1)).
Proof.
unfold open_object_wrt_object; default_simp.
Qed.

Hint Resolve subst_object_intro : lngen.

Lemma subst_kind_intro :
forall x1 K1 M1,
  x1 `notin` fv_kind K1 ->
  open_kind_wrt_object K1 M1 = subst_kind M1 x1 (open_kind_wrt_object K1 (object_var_f x1)).
Proof.
unfold open_kind_wrt_object; default_simp.
Qed.

Hint Resolve subst_kind_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
