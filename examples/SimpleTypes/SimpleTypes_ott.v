(* generated by Ott 0.32, locally-nameless lngen from: SimpleTypes.ott *)
Require Import Metalib.Metatheory.
(** syntax *)
Definition expvar : Set := var.

Inductive typ : Set := 
 | base : typ
 | arrow (T1:typ) (T2:typ).

Inductive exp : Set := 
 | var_b (_:nat)
 | var_f (x:expvar)
 | abs (T:typ) (e:exp)
 | app (e1:exp) (e2:exp).

Definition typing_env : Set := list (atom*typ).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
Definition is_value_of_exp (e_5:exp) : Prop :=
  match e_5 with
  | (var_b nat) => False
  | (var_f x) => False
  | (abs T e) => (True)
  | (app e1 e2) => False
end.

(** arities *)
(** opening up abstractions *)
Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => var_b nat
        | inleft (right _) => e_5
        | inright _ => var_b (nat - 1)
      end
  | (var_f x) => var_f x
  | (abs T e) => abs T (open_exp_wrt_exp_rec (S k) e_5 e)
  | (app e1 e2) => app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** closing up abstractions *)
Fixpoint close_exp_wrt_exp_rec (k:nat) (e_5:var) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (var_b nat) => 
       if (lt_dec nat k) 
         then var_b nat
         else var_b (S nat)
  | (var_f x) => if (e_5 === x) then (var_b k) else (var_f x)
  | (abs T e) => abs T (close_exp_wrt_exp_rec (S k) e_5 e)
  | (app e1 e2) => app (close_exp_wrt_exp_rec k e_5 e1) (close_exp_wrt_exp_rec k e_5 e2)
end.

Definition close_exp_wrt_exp e__6 e_5 := close_exp_wrt_exp_rec 0 e__6 e_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_var_f : forall (x:expvar),
     (lc_exp (var_f x))
 | lc_abs : forall (T:typ) (e:exp),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (var_f x) )  )  ->
     (lc_exp (abs T e))
 | lc_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (app e1 e2)).
(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (var_b nat) => {}
  | (var_f x) => {{x}}
  | (abs T e) => (fv_exp e)
  | (app e1 e2) => (fv_exp e1) \u (fv_exp e2)
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:expvar) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (var_b nat) => var_b nat
  | (var_f x) => (if eq_var x x5 then e_5 else (var_f x))
  | (abs T e) => abs T (subst_exp e_5 x5 e)
  | (app e1 e2) => app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
end.


(** definitions *)

(* defns Jtyping *)
Inductive typing : typing_env -> exp -> typ -> Prop :=    (* defn typing *)
 | typing_var : forall (G:typing_env) (x:expvar) (T:typ),
      binds ( x ) ( T ) ( G )  ->
      uniq ( G )  ->
     typing G (var_f x) T
 | typing_abs : forall (L:vars) (G:typing_env) (T1:typ) (e:exp) (T2:typ),
      ( forall x , x \notin  L  -> typing  ( x ~ T1  ++  G )   ( open_exp_wrt_exp e (var_f x) )  T2 )  ->
     typing G (abs T1 e) (arrow T1 T2)
 | typing_app : forall (G:typing_env) (e1 e2:exp) (T2 T1:typ),
     typing G e1 (arrow T1 T2) ->
     typing G e2 T1 ->
     typing G (app e1 e2) T2.

(* defns Jop *)
Inductive step : exp -> exp -> Prop :=    (* defn step *)
 | step_app_1 : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (app e1 e2) (app e1' e2)
 | step_app_2 : forall (e2 e2' v1:exp),
     is_value_of_exp v1 ->
     lc_exp v1 ->
     step e2 e2' ->
     step (app v1 e2) (app v1 e2')
 | step_beta : forall (T:typ) (e1 v2:exp),
     is_value_of_exp v2 ->
     lc_exp (abs T e1) ->
     lc_exp v2 ->
     step (app  ( (abs T e1) )  v2)  (open_exp_wrt_exp  e1   v2 ) .


(** infrastructure *)
#[export] Hint Constructors typing step lc_exp : core.


