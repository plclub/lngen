Add LoadPath "metatheory".
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Metatheory.
Require Import Lambda_inf.
Require Import Lambda_ott.


(* *********************************************************************** *)
(** * Lemmas *)

(** Ideally, LNgen would generate these lemmas.  They're nothing more
    than casting some lemmas stated for [lc_exp] into lemmas stated for
    [lc_set_exp]. *)

Lemma lc_set_abs_exists : forall x1 e1,
  lc_set_exp (open_exp_wrt_exp e1 (var_f x1)) -> lc_set_exp (abs e1).
Proof.
  eauto using lc_set_exp_of_lc_exp, lc_exp_of_lc_set_exp, lc_abs_exists.
Qed.

Lemma lc_set_exp_unique : forall e1 (lcp1 lcp2 : lc_set_exp e1),
  lcp1 = lcp2.
Proof.
apply_mutual_ind lc_set_exp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

Lemma subst_exp_lc_set_exp : forall e1 e2 x1,
  lc_set_exp e1 ->
  lc_set_exp e2 ->
  lc_set_exp (subst_exp e2 x1 e1).
Proof.
  auto using lc_set_exp_of_lc_exp, lc_exp_of_lc_set_exp, subst_exp_lc_exp.
Qed.


(* *********************************************************************** *)
(** * Beta reduction *)

Fixpoint beta (e : exp) (lcp : lc_set_exp e) {struct lcp} : exp :=
  match lcp with
    | lc_set_var_f x => var_f x
    | lc_set_app e1 e2 lcp1 lcp2 =>
      match beta e1 lcp1 with
        | abs e1' => open_exp_wrt_exp e1' (beta e2 lcp2)
        | _ => app (beta e1 lcp1) (beta e2 lcp2)
      end
    | lc_set_abs e1 lcp1 =>
      let (x, _) := atom_fresh (fv_exp e1) in
      abs (close_exp_wrt_exp x (beta (open_exp_wrt_exp e1 (var_f x)) (lcp1 x)))
  end.


(* *********************************************************************** *)
(** * Model of Gordon and Melham's "Five Axioms" *)

(** ** Definitions *)

Definition Term := (sigT lc_set_exp).

Definition Var (x : expvar) : Term :=
  existT _ (var_f x) (lc_set_var_f x).

Definition App (t1 t2 : Term) : Term :=
  let (e1, lcp1) := t1 in
  let (e2, lcp2) := t2 in
  existT _ (app e1 e2) (lc_set_app e1 e2 lcp1 lcp2).

Definition Lam (x : expvar) (t : Term) : Term :=
  let (e1, lcp1) := t in
  existT _ (abs (close_exp_wrt_exp x e1))
    (lc_set_abs_exists x (close_exp_wrt_exp x e1)
      (eq_rec_r _ lcp1 (open_exp_wrt_exp_close_exp_wrt_exp e1 x))).

Definition Fv (t : Term) : vars :=
  let (e1, _) := t in
  fv_exp e1.

Definition Subst (t : Term) (ux : Term * expvar) : Term :=
  let (e1, lcp1) := t in
  let (u, x) := ux in
  let (e2, lcp2) := u in
  existT _ (subst_exp e2 x e1) (subst_exp_lc_set_exp e1 e2 x lcp1 lcp2).

Definition Abs (f : expvar -> Term) : Term :=
  let (arbitrary, _) := atom_fresh empty in
  let (e1, _) := f arbitrary in
  let (y, _) := atom_fresh (fv_exp e1) in
  let (e2, lcp2) := f y in
  existT _ (abs (close_exp_wrt_exp y e2))
    (lc_set_abs_exists y (close_exp_wrt_exp y e2)
      (eq_rec_r _ lcp2 (open_exp_wrt_exp_close_exp_wrt_exp e2 y))).

(** ** Reasoning about uniqueness of [lc_exp] proofs *)

Lemma Term_eq : forall e1 lcp1 e2 lcp2,
  e1 = e2 ->
  existT lc_set_exp e1 lcp1 = existT lc_set_exp e2 lcp2.
Proof.
  intros e1 lcp1 e2 lcp2 Eq.
  subst e1. f_equal. apply lc_set_exp_unique.
Qed.

(** ** Axiom 1: Free variables *)

Theorem Fv1 : forall x,
  Fv (Var x) = singleton x.
Proof. reflexivity. Qed.

Theorem Fv2 : forall t1 t2,
  Fv (App t1 t2) = Fv t1 `union` Fv t2.
Proof. destruct t1. destruct t2. reflexivity. Qed.

Theorem Fv3 : forall x t,
  Fv (Lam x t) [=] remove x (Fv t).
Proof. destruct t. simpl. apply fv_exp_close_exp_wrt_exp. Qed.

(** ** Axiom 2: Substitution *)

Theorem Subst1 : forall x u,
  Subst (Var x) (u, x) = u.
Proof. destruct u. simpl. apply Term_eq. default_simp. Qed.

Theorem Subst2 : forall x y u,
  x <> y ->
  Subst (Var y) (u, x) = Var y.
Proof. intros. destruct u. simpl. apply Term_eq. default_simp. Qed.

Theorem Subst3 : forall t1 t2 u x,
  Subst (App t1 t2) (u, x) = App (Subst t1 (u, x)) (Subst t2 (u, x)).
Proof.
  destruct t1. destruct t2. destruct u.
  intros. simpl. apply Term_eq. reflexivity.
Qed.

Theorem Subst4 : forall t u x,
  Subst (Lam x t) (u, x) = Lam x t.
Proof.
  destruct t. destruct u.
  intros. simpl. apply Term_eq.
  rewrite subst_exp_fresh_eq.
    reflexivity.
    rewrite fv_exp_close_exp_wrt_exp. solve_notin.
Qed.

Theorem Subst5 : forall y t u x,
  x <> y ->
  y `notin` Fv u ->
  Subst (Lam y t) (u, x) = Lam y (Subst t (u, x)).
Proof.
  destruct t. destruct u.
  intros. simpl. apply Term_eq.
  rewrite subst_exp_close_exp_wrt_exp; trivial.
  apply lc_exp_of_lc_set_exp; trivial.
Qed.

(** ** Axiom 3: Alpha-conversion *)

Theorem Alpha : forall x t y,
  y `notin` Fv (Lam x t) ->
  Lam x t = Lam y (Subst t (Var y, x)).
Proof.
  destruct t.
  intros. simpl. apply Term_eq.
  rewrite subst_exp_spec.
  rewrite close_exp_wrt_exp_open_exp_wrt_exp; trivial.
Qed.

(** ** Axiom 4: Recursion scheme *)

Section FiveAxiomsRecursion.

Variable R : Set.
Variable fvar : expvar -> R.
Variable fapp : R -> R -> Term -> Term -> R.
Variable fabs : (expvar -> R) -> (expvar -> Term) -> R.

Definition gm_rec (t : Term) : R :=
  let (e, lcp) := t in
  lc_set_exp_rec (fun _ _ => R)
    fvar
    (fun e1 e2 lcp1 r1 lcp2 r2 => fapp r1 r2 (existT _ e1 lcp1) (existT _ e2 lcp2))
    (fun e1 lcp1 r1 => fabs r1 (fun x => existT _ (open_exp_wrt_exp e1 (var_f x)) (lcp1 x)))
    e
    lcp.

Theorem Recursion1 : forall x,
  gm_rec (Var x) = fvar x.
Proof. reflexivity. Qed.

Theorem Recursion2 : forall t1 t2,
  gm_rec (App t1 t2) = fapp (gm_rec t1) (gm_rec t2) t1 t2.
Proof. destruct t1. destruct t2. reflexivity. Qed.

Theorem Recursion3 : forall x t,
  gm_rec (Lam x t) = fabs (fun y => gm_rec (Subst t (Var y, x))) (fun y => Subst t (Var y, x)).
Proof.
  (* Allow [gm_rec] and everything else to reduce. *)
  unfold Lam. destruct t as [e1 lcp1]. simpl gm_rec at 1.

  (* [lc_set_exp_rec] will reduce once we invert the proof. *)
  match goal with |- lc_set_exp_rec _ _ _ _ _ ?pf = _ => set (proof := pf) end.
  dependent inversion proof.
  simpl lc_set_exp_rec.

  (* [fabs] takes two arguments.  Prove them each equal to each other. *)
  f_equal.

  (* Argument 1: Go through contortions to apply [subst_spec]. *)
  apply functional_extensionality; intros z.
  set (t := (existT _ (open_exp_wrt_exp (close_exp_wrt_exp x e1) (var_f z)) (l z))).
  match goal with |- ?lhs = _ => change lhs with (gm_rec t) end.
  f_equal; unfold t; simpl.
  apply Term_eq.
  rewrite subst_exp_spec.
  reflexivity.

  (* Argument 2: Straightforward. *)
  apply functional_extensionality; intros.
  simpl.
  apply Term_eq.
  rewrite subst_exp_spec.
  reflexivity.
Qed.

End FiveAxiomsRecursion.

(** ** Axiom 5: Abstraction *)

Theorem Abstraction : forall x u,
  Abs (fun y => Subst u (Var y, x)) = Lam x u.
Proof.
  intros x u. unfold Abs, Subst, Lam, Var. destruct u.
  do 2 destruct_exists. apply Term_eq.
  rewrite subst_exp_spec.
  rewrite close_exp_wrt_exp_open_exp_wrt_exp.
    reflexivity.
    rewrite fv_exp_close_exp_wrt_exp.
      assert (remove x (fv_exp x0) [<=] fv_exp (subst_exp (var_f x1) x x0)).
        apply fv_exp_subst_exp_lower.
      fsetdec.
Qed.
