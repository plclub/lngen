
Require Export Coq.Program.Equality.
Require Export SimpleTypes_inf.
Require Import String.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x : typing_env => dom x) in
  let D1 := gather_atoms_with (fun x => fv_exp x) in
  constr:(A \u B \u C \u D1).


(* *********************************************************************** *)
(** * Regularity lemmas *)

Lemma typing_regular_1 : forall G e T,
  typing G e T ->
  lc_exp e.
Proof. induction 1; eauto. Qed.

Hint Resolve typing_regular_1 : core.

Lemma typing_regular_2 : forall G e T,
  typing G e T ->
  uniq G.
Proof.
  induction 1; eauto.
  pick fresh z. lapply (H0 z); solve_uniq.
Qed.

Hint Resolve typing_regular_2 : core.

Lemma step_regular_1 : forall e1 e2,
  step e1 e2 ->
  lc_exp e1.
Proof. induction 1; eauto. Qed.

Hint Resolve step_regular_1 : core.

Lemma step_regular_2 : forall e1 e2,
  step e1 e2 ->
  lc_exp e1.
Proof. induction 1; eauto. Qed.

Hint Resolve step_regular_2 : core.


(* *********************************************************************** *)
(** * Main proofs *)

Lemma typing_weakening : forall F E G e T,
  typing (F ++ G) e T ->
  uniq (F ++ E ++ G) ->
  typing (F ++ E ++ G) e T.
Proof.
  intros until 1. dependent induction H; intros; eauto.
  Case "typing_abs".
   pick fresh x and apply typing_abs.
   rewrite_env ((x ~ T1 ++ F) ++ E ++ G).
   apply_first_hyp; simpl_env; auto.
Qed.

Lemma typing_subst : forall F G e u S T x,
  typing (F ++ x ~ S ++ G) e T ->
  typing G u S ->
  typing (F ++ G) (subst_exp u x e) T.
Proof with eauto.
  intros until 1. dependent induction H; intros; simpl subst_exp...
  Case "typing_var".
    destruct (x0 == x); try subst x0.
    SCase "x = x0".
      analyze_binds_uniq H.
      apply typing_weakening with (F := nil)...
    SCase "x <> x0".
      analyze_binds_uniq H...
  Case "typing_abs".
    pick fresh z and apply typing_abs.
    rewrite_env ((z ~ T1 ++ F) ++ G).
    rewrite subst_exp_open_exp_wrt_exp_var...
    apply H0 with (S0 := S)...
Qed.

Lemma preservation : forall G e1 e2 T,
  typing G e1 T ->
  step e1 e2 ->
  typing G e2 T.
Proof with eauto.
  intros G e1 e2 T H. revert e2.
  dependent induction H; try solve [intros ? J; inversion J].
  Case "typing_app".
    intros ? J; inversion J; subst...
    inversion H; subst.
    pick fresh z.
    rewrite (subst_exp_intro z)...
    eapply typing_subst with (F := nil); simpl_env...
Qed.

Lemma progress : forall e1 T,
  typing nil e1 T ->
  (exists e2, step e1 e2) \/ is_value_of_exp e1.
Proof with eauto 10.
  intros e1 T H.
  dependent induction H; simpl...
  Case "typing_app".
    destruct IHtyping1 as [[e1' ?] | ?]...
    destruct IHtyping2 as [[e2' ?] | ?]...
    destruct e1; simpl in H1; inversion H1...
Qed.
