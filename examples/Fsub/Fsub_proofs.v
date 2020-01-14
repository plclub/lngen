(** System F with subtyping, extended with let-bindings and sum types.

    Authors: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    Table of contents:
      - #<a href="##wft">Properties of wf_typ</a>#
      - #<a href="##oktwft">Properties of wf_env and wf_typ</a>#
      - #<a href="##okt">Properties of wf_env</a>#
      - #<a href="##subst">Properties of substitution</a>#
      - #<a href="##regularity">Regularity lemmas</a>#
      - #<a href="##auto">Automation</a># 
      - #<a href="##subtyping">Properties of subtyping</a>#
      - #<a href="##typing">Properties of typing</a>#
      - #<a href="##preservation">Preservation</a>#
      - #<a href="##progress">Progress</a># *)


Require Export Fsub_inf.
Require Import String.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x : env => dom x) in
  let D1 := gather_atoms_with (fun x => fv_typ_in_typ x) in
  let D2 := gather_atoms_with (fun x => fv_typ_in_exp x) in
  let D3 := gather_atoms_with (fun x => fv_typ_in_binding x) in
  let D4 := gather_atoms_with (fun x => fv_exp_in_exp x) in
  constr:(A \u B \u C \u D1 \u D2 \u D3 \u D4).


(* ********************************************************************** *)
(** * Compatability with the original development: Hints, notations, etc. *)

Coercion typ_var_b : nat >-> typ.
Coercion typ_var_f : typvar >-> typ.
Coercion exp_var_b : nat >-> exp.
Coercion exp_var_f : expvar >-> exp.

Notation empty := (@nil (atom * binding)).

Hint Extern 1 (binds _ (?F (subst_typ_in_typ ?X ?U ?T)) _) =>
  unsimpl (subst_typ_in_binding X U (F T)) : core.


(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

(** If a type is well-formed in an environment, then it is locally
    closed. *)

Lemma type_from_wf_typ : forall E T,
  wf_typ E T -> lc_typ T.
Proof.
  intros E T H; induction H; eauto.
Qed.

(** The remaining properties are analogous to the properties that we
    need to show for the subtyping and typing relations. *)

Lemma wf_typ_weakening : forall T E F G,
  wf_typ (G ++ E) T ->
  uniq (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) T.
Proof with simpl_env; eauto.
  intros T E F G Hwf_typ Hk.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction Hwf_typ; intros G Hok Heq; subst...
  Case "type_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    apply H0...
Qed.

Lemma wf_typ_weaken_head : forall T E F,
  wf_typ E T ->
  uniq (F ++ E) ->
  wf_typ (F ++ E) T.
Proof.
  intros.
  rewrite_env (empty ++ F++ E).
  auto using wf_typ_weakening.
Qed.

Lemma wf_typ_narrowing : forall V U T E F X,
  wf_typ (F ++ X ~ bind_sub V ++ E) T ->
  wf_typ (F ++ X ~ bind_sub U ++ E) T.
Proof with simpl_env; eauto.
  intros V U T E F X Hwf_typ.
  remember (F ++ X ~ bind_sub V ++ E) as G.
  generalize dependent F.
  induction Hwf_typ; intros F Heq; subst...
  Case "wf_typ_var".
    analyze_binds H...
  Case "typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    apply H0...
Qed.

Lemma wf_typ_strengthening : forall E F x U T,
 wf_typ (F ++ x ~ bind_typ U ++ E) T ->
 wf_typ (F ++ E) T.
Proof with simpl_env; eauto.
  intros E F x U T H.
  remember (F ++ x ~ bind_typ U ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...
  Case "wf_typ_var".
    analyze_binds H...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    apply H1...
Qed.

Lemma wf_typ_subst_typ_in_binding : forall F Q E Z P T,
  wf_typ (F ++ Z ~ bind_sub Q ++ E) T ->
  wf_typ E P ->
  uniq (map (subst_typ_in_binding P Z) F ++ E) ->
  wf_typ (map (subst_typ_in_binding P Z) F ++ E) (subst_typ_in_typ P Z T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_sub Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_typ_in_typ...
  Case "wf_typ_var".
    destruct (X == Z); subst...
    SCase "X <> Z".
      analyze_binds H...
      apply wf_typ_var with (U := subst_typ_in_typ P Z U)...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var...
    rewrite_env (map (subst_typ_in_binding P Z) (Y ~ bind_sub T1 ++ F) ++ E).
    apply H0...
Qed.

Lemma wf_typ_open : forall E U T1 T2,
  uniq E ->
  wf_typ E (typ_all T1 T2) ->
  wf_typ E U ->
  wf_typ E (open_typ_wrt_typ T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 Ok WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_typ_in_typ_intro X)...
  rewrite_env (map (subst_typ_in_binding U X) empty ++ E).
  eapply wf_typ_subst_typ_in_binding...
Qed.


(* ********************************************************************** *)
(** * #<a name="oktwft"></a># Properties of [wf_env] and [wf_typ] *)

Lemma uniq_from_wf_env : forall E,
  wf_env E ->
  uniq E.
Proof.
  intros E H; induction H; auto.
Qed.

(** We add [uniq_from_wf_env] as a hint here since it helps blur the
    distinction between [wf_env] and [uniq] in proofs.  The lemmas in
    the MetatheoryEnv library use [uniq], whereas here we naturally
    have (or can easily show) the stronger [wf_env].  Thus,
    [uniq_from_wf_env] serves as a bridge that allows us to use the
    environments library. *)

Hint Resolve uniq_from_wf_env : core.

Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  wf_typ E U.
Proof with auto using wf_typ_weaken_head.
  induction 1; intros J; analyze_binds J...
  injection BindsTacVal; intros; subst...
Qed.

Lemma wf_typ_from_wf_env_typ : forall x T E,
  wf_env (x ~ bind_typ T ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

Lemma wf_typ_from_wf_env_sub : forall x T E,
  wf_env (x ~ bind_sub T ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.


(* ********************************************************************** *)
(** * #<a name="okt"></a># Properties of [wf_env] *)

(** These properties are analogous to the properties that we need to
    show for the subtyping and typing relations. *)

Lemma wf_env_narrowing : forall V E F U X,
  wf_env (F ++ X ~ bind_sub V ++ E) ->
  wf_typ E U ->
  wf_env (F ++ X ~ bind_sub U ++ E).
Proof with eauto using wf_typ_narrowing.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_strengthening : forall x T E F,
  wf_env (F ++ x ~ bind_typ T ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_typ_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_subst_typ_in_binding : forall Q Z P E F,
  wf_env (F ++ Z ~ bind_sub Q ++ E) ->
  wf_typ E P ->
  wf_env (map (subst_typ_in_binding P Z) F ++ E).
Proof with eauto 6 using wf_typ_subst_typ_in_binding.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_typ_in_binding...
Qed.


(* ********************************************************************** *)
(** * #<a name="subst"></a># Environment is unchanged by substitution for a fresh name *)

Lemma notin_fv_typ_in_typ_open : forall (Y X : typvar) T,
  X `notin` fv_typ_in_typ (open_typ_wrt_typ T Y) ->
  X `notin` fv_typ_in_typ T.
Proof.
 intros Y X T. unfold open_typ_wrt_typ.
 generalize 0.
 induction T; simpl; intros k Fr; eauto.
Qed.

Lemma notin_fv_wf : forall E (X : typvar) T,
  wf_typ E T ->
  X `notin` dom E ->
  X `notin` fv_typ_in_typ T.
Proof with auto.
  intros E X T Wf_typ.
  induction Wf_typ; intros Fr; simpl...
  Case "wf_typ_var".
    assert (X0 `in` (dom E))...
    eapply binds_In; eauto. fsetdec.
  Case "wf_typ_all".
    apply notin_union...
    pick fresh Y.
    apply (notin_fv_typ_in_typ_open Y)...
Qed.

Lemma map_subst_typ_in_binding_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_typ_in_binding P Z) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
    rewrite subst_typ_in_typ_fresh_eq... eapply notin_fv_wf; eauto.
  rewrite <- IHwf_env...
    rewrite subst_typ_in_typ_fresh_eq... eapply notin_fv_wf; eauto.
Qed.


(* ********************************************************************** *)
(** * #<a name="regularity"></a># Regularity of relations *)

Lemma sub_regular : forall E S T,
  sub E S T ->
  wf_env E /\ wf_typ E S /\ wf_typ E T.
Proof with simpl_env; try solve [auto | intuition auto].
  intros E S T H.
  induction H...
  Case "sub_trans_tvar".
    intuition eauto.
  Case "sub_all".
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh Y and apply wf_typ_all...
      destruct (H1 Y)...
      rewrite_env (empty ++ Y ~ bind_sub S1 ++ E).
      apply (wf_typ_narrowing T1)...
    SCase "Third of original three conjuncts".
      pick fresh Y and apply wf_typ_all...
      destruct (H1 Y)...
Qed.

Lemma typing_regular : forall E e T,
  typing E e T ->
  wf_env E /\ lc_exp e /\ wf_typ E T.
Proof with simpl_env; try solve [auto | intuition auto].
  intros E e T H; induction H...
  Case "typing_var".
    repeat split...
    eauto using wf_typ_from_binds_typ.
  Case "typing_abs".
    pick fresh y.
    destruct (H0 y) as [Hok [J K]]...
    repeat split. inversion Hok...
    SCase "Second of original three conjuncts".
      pick fresh x.
      apply (lc_exp_abs_exists x).
        eauto using type_from_wf_typ, wf_typ_from_wf_env_typ.
        destruct (H0 x)...
    SCase "Third of original three conjuncts".
      apply wf_typ_arrow; eauto using wf_typ_from_wf_env_typ.
      rewrite_env (empty ++ E).
      eapply wf_typ_strengthening; simpl_env; eauto.
  Case "typing_app".
    repeat split...
    destruct IHtyping1 as [_ [_ K]].
    inversion K...
  Case "typing_tabs".
    pick fresh Y.
    destruct (H0 Y) as [Hok [J K]]...
    inversion Hok; subst.
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh X.
      apply (lc_exp_tabs_exists X).
        eauto using type_from_wf_typ, wf_typ_from_wf_env_sub...
        destruct (H0 X)...
    SCase "Third of original three conjuncts".
      pick fresh Z and apply wf_typ_all...
      destruct (H0 Z)...
  Case "typing_tapp".
    destruct (sub_regular _ _ _ H0) as [R1 [R2 R3]].
    repeat split...
    SCase "Second of original three conjuncts".
      apply lc_exp_tapp...
      eauto using type_from_wf_typ.
    SCase "Third of original three conjuncts".
      destruct IHtyping as [R1' [R2' R3']].
      eapply wf_typ_open; eauto.
  Case "typing_sub".
    repeat split...
    destruct (sub_regular _ _ _ H0)...
  Case "typing_let".
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh y.
      apply (lc_exp_let_exists y)...
      destruct (H1 y) as [K1 [K2 K3]]...
    SCase "Third of original three conjuncts".
      pick fresh y.
      destruct (H1 y) as [K1 [K2 K3]]...
      rewrite_env (empty ++ E).
      eapply wf_typ_strengthening; simpl_env; eauto.
  Case "typing_case".
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh x.
      pick fresh y.
      apply (lc_exp_case_exists x y)...
        destruct (H1 x) as [? [? ?]]...
        destruct (H3 y) as [? [? ?]]...
    SCase "Third of original three conjuncts".
      pick fresh y.
      destruct (H1 y) as [K1 [K2 K3]]...
      rewrite_env (empty ++ E).
      eapply wf_typ_strengthening; simpl_env; eauto.
Qed.

Lemma red_regular : forall e e',
  red e e' ->
  lc_exp e /\ lc_exp e'.
Proof.
  intros e e' H.
  induction H; intuition eauto 6 with lngen.
Qed.


(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** The lemma [uniq_from_wf_env] was already added above as a hint
    since it helps blur the distinction between [wf_env] and [uniq] in
    proofs.

    As currently stated, the regularity lemmas are ill-suited to be
    used with [auto] and [eauto] since they end in conjunctions.  Even
    if we were, for example, to split [sub_regularity] into three
    separate lemmas, the resulting lemmas would be usable only by
    [eauto] and there is no guarantee that [eauto] would be able to
    find proofs effectively.  Thus, the hints below apply the
    regularity lemmas and [type_from_wf_typ] to discharge goals about
    local closure and well-formedness, but in such a way as to
    minimize proof search.

    The first hint introduces an [wf_env] fact into the context.  It
    works well when combined with the lemmas relating [wf_env] and
    [wf_typ].  We choose to use those lemmas explicitly via [(auto
    using ...)] tactics rather than add them as hints.  When used this
    way, the explicitness makes the proof more informative rather than
    more cluttered (with useless details).

    The other three hints try outright to solve their respective
    goals. *)

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: sub _ _ _ |- _ => apply (proj1 (sub_regular _ _ _ H))
  | H: typing _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ H))
  end : core.

Hint Extern 1 (wf_typ ?E ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ H)))
  | H: sub E T _ |- _ => apply (proj1 (proj2 (sub_regular _ _ _ H)))
  | H: sub E _ T |- _ => apply (proj2 (proj2 (sub_regular _ _ _ H)))
  end : core.

Hint Extern 1 (lc_typ ?T) =>
  let go E := apply (type_from_wf_typ E); auto in
  match goal with
  | H: typing ?E _ T |- _ => go E
  | H: sub ?E T _ |- _ => go E
  | H: sub ?E _ T |- _ => go E
  end : core.

Hint Extern 1 (lc_exp ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ H)))
  | H: red ?e _ |- _ => apply (proj1 (red_regular _ _ H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular _ _ H))
  end : core.


(* ********************************************************************** *)
(** * #<a name="subtyping"></a># Properties of subtyping *)


(* ********************************************************************** *)
(** ** Reflexivity (1) *)

Lemma sub_reflexivity : forall E T,
  wf_env E ->
  wf_typ E T ->
  sub E T T.
Proof with eauto.
  intros E T Ok Wf.
  induction Wf...
  pick fresh Y and apply sub_all...
Qed.


(* ********************************************************************** *)
(** ** Weakening (2) *)

Lemma sub_weakening : forall E F G S T,
  sub (G ++ E) S T ->
  wf_env (G ++ F ++ E) ->
  sub (G ++ F ++ E) S T.
Proof with simpl_env; auto using wf_typ_weakening.
  intros E F G S T Sub Ok.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Sub; intros G Ok EQ; subst...
  Case "sub_trans_tvar".
    apply sub_trans_tvar with (U := U)...
  Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- app_assoc.
    apply H0...
Qed.


(* ********************************************************************** *)
(** ** Narrowing and transitivity (3) *)

Definition transitivity_on Q := forall E S T,
  sub E S Q -> sub E Q T -> sub E S T.

Lemma sub_narrowing_aux : forall Q F E Z P S T,
  transitivity_on Q ->
  sub (F ++ Z ~ bind_sub Q ++ E) S T ->
  sub E P Q ->
  sub (F ++ Z ~ bind_sub P ++ E) S T.
Proof with simpl_env; eauto using wf_typ_narrowing, wf_env_narrowing.
  intros Q F E Z P S T TransQ SsubT PsubQ.
  remember (F ++ Z ~ bind_sub Q ++ E) as G. generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "sub_trans_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply sub_trans_tvar with (U := P); [ eauto using fresh_mid_head | ].
      apply TransQ.
      SSCase "P <: Q".
        rewrite_env (empty ++ (F ++ Z ~ bind_sub P) ++ E).
        apply sub_weakening...
      SSCase "Q <: T".
        analyze_binds_uniq H.
        injection BindsTacVal; intros; subst...
    SCase "X <> Z".
      apply sub_trans_tvar with (U := U)...
  Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- app_assoc.
    apply H0...
Qed.

Lemma sub_transitivity : forall Q,
  transitivity_on Q.
Proof with simpl_env; auto.
  unfold transitivity_on.
  intros Q E S T SsubQ QsubT.
  assert (W : lc_typ Q) by auto.
  generalize dependent T.
  generalize dependent S.
  generalize dependent E.
  remember Q as Q' in |- *.
  generalize dependent Q'.
  induction W;
    intros Q' EQ E S SsubQ;
    induction SsubQ; try discriminate; inversion EQ; subst;
    intros T' QsubT;
    inversion QsubT; subst; eauto 4 using sub_trans_tvar.
  Case "sub_all / sub_top".
    assert (sub E (typ_all S1 S2) (typ_all T1 T2)).
      SCase "proof of assertion".
      pick fresh y and apply sub_all...
    auto.
  Case "sub_all / sub_all".
    pick fresh Y and apply sub_all.
    SCase "bounds".
      eauto.
    SCase "bodies".
      specialize (H0 Y). (* BEA: was an [lapply]+[apply] step before *)
      apply (H0 (open_typ_wrt_typ T2 (typ_var_f Y)))...
      rewrite_env (empty ++ Y ~ bind_sub T0 ++ E).
      apply (sub_narrowing_aux T1)...
      unfold transitivity_on.
      auto using (IHW T1).
Qed.

Lemma sub_narrowing : forall Q E F Z P S T,
  sub E P Q ->
  sub (F ++ Z ~ bind_sub Q ++ E) S T ->
  sub (F ++ Z ~ bind_sub P ++ E) S T.
Proof.
  intros.
  eapply sub_narrowing_aux; eauto.
  apply sub_transitivity.
Qed.


(* ********************************************************************** *)
(** ** Type substitution preserves subtyping (10) *)

Lemma sub_through_subst_typ_in_typ : forall Q E F Z S T P,
  sub (F ++ Z ~ bind_sub Q ++ E) S T ->
  sub E P Q ->
  sub (map (subst_typ_in_binding P Z) F ++ E) (subst_typ_in_typ P Z S) (subst_typ_in_typ P Z T).
Proof with
      simpl_env;
      eauto 4 using wf_typ_subst_typ_in_binding, wf_env_subst_typ_in_binding, wf_typ_weaken_head.
  intros Q E F Z S T P SsubT PsubQ.
  remember (F ++ Z ~ bind_sub Q ++ E) as G.
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl subst_typ_in_typ...
  Case "sub_top".
    apply sub_top...
  Case "sub_refl_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply sub_reflexivity...
    SCase "X <> Z".
      apply sub_reflexivity...
      inversion H0; subst.
      analyze_binds H3...
      apply wf_typ_var with (U := subst_typ_in_typ P Z U)...
  Case "sub_trans_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply (sub_transitivity Q).
      SSCase "left branch".
        rewrite_env (empty ++ map (subst_typ_in_binding P Z) G ++ E).
        apply sub_weakening...
      SSCase "right branch".
        rewrite <- (subst_typ_in_typ_fresh_eq Q P Z)...
          analyze_binds_uniq H.
            inversion BindsTacVal; subst...
          apply (notin_fv_wf E); eauto using fresh_mid_tail.
    SCase "X <> Z".
      apply sub_trans_tvar with (U := subst_typ_in_typ P Z U)...
      rewrite (map_subst_typ_in_binding_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      analyze_binds H...
  Case "sub_all".
    pick fresh X and apply sub_all...
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var...
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var...
    rewrite_env (map (subst_typ_in_binding P Z) (X ~ bind_sub T1 ++ G) ++ E).
    apply H0...
Qed.


(* ********************************************************************** *)
(** * #<a name="typing"></a># Properties of typing *)


(* ********************************************************************** *)
(** ** Weakening (5) *)

Lemma typing_weakening : forall E F G e T,
  typing (G ++ E) e T ->
  wf_env (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof with simpl_env;
           eauto using wf_typ_weakening,
                       wf_typ_from_wf_env_typ,
                       wf_typ_from_wf_env_sub,
                       sub_weakening.
  intros E F G e T Typ.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Typ; intros G EQ Ok; subst...
  Case "typing_abs".
    pick fresh x and apply typing_abs.
    lapply (H x); [intros K | auto].
    rewrite <- app_assoc.
    apply (H0 x)...
  Case "typing_tabs".
    pick fresh X and apply typing_tabs.
    lapply (H X); [intros K | auto].
    rewrite <- app_assoc.
    apply (H0 X)...
  Case "typing_let".
    pick fresh x and apply typing_let...
    lapply (H0 x); [intros K | auto].
    rewrite <- app_assoc.
    apply H0...
  Case "typing_case".
    pick fresh x and apply typing_case...
    SCase "inl branch".
      lapply (H0 x); [intros K | auto].
      rewrite <- app_assoc.
      apply H0...
      assert (J : wf_typ (G ++ F ++ E) (typ_sum T1 T2))...
      inversion J...
    SCase "inr branch".
      lapply (H2 x); [intros K | auto].
      rewrite <- app_assoc.
      apply H2...
      assert (J : wf_typ (G ++ F ++ E) (typ_sum T1 T2))...
      inversion J...
Qed.


(* ********************************************************************** *)
(** ** Strengthening (6) *)

Lemma sub_strengthening : forall x U E F S T,
  sub (F ++ x ~ bind_typ U ++ E) S T ->
  sub (F ++ E) S T.
Proof with eauto using wf_typ_strengthening, wf_env_strengthening.
  intros x U E F S T SsubT.
  remember (F ++ x ~ bind_typ U ++ E) as E'.
  generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "sub_trans_tvar".
    apply sub_trans_tvar with (U := U0)...
    analyze_binds H...
  Case "sub_all".
    pick fresh X and apply sub_all...
    rewrite <- app_assoc.
    apply H0...
Qed.


(************************************************************************ *)
(** ** Narrowing for typing (7) *)

Lemma typing_narrowing : forall Q E F X P e T,
  sub E P Q ->
  typing (F ++ X ~ bind_sub Q ++ E) e T ->
  typing (F ++ X ~ bind_sub P ++ E) e T.
Proof with eauto 6 using wf_env_narrowing, wf_typ_narrowing, sub_narrowing.
  intros Q E F X P e T PsubQ Typ.
  remember (F ++ X ~ bind_sub Q ++ E) as E'.
  generalize dependent F.
  induction Typ; intros F EQ; subst...
  Case "typing_var".
    analyze_binds H0...
  Case "typing_abs".
    pick fresh y and apply typing_abs.
    rewrite <- app_assoc.
    apply H0...
  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    rewrite <- app_assoc.
    apply H0...
  Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite <- app_assoc.
    apply H0...
  Case "typing_case".
    pick fresh y and apply typing_case...
    SCase "inl branch".
      rewrite <- app_assoc.
      apply H0...
    SCase "inr branch".
      rewrite <- app_assoc.
      apply H2...
Qed.


(************************************************************************ *)
(** ** Substitution preserves typing (8) *)

Lemma typing_through_subst_exp_in_exp : forall U E F x T e u,
  typing (F ++ x ~ bind_typ U ++ E) e T ->
  typing E u U ->
  typing (F ++ E) (subst_exp_in_exp u x e) T.
(* begin show *)

(** We provide detailed comments for the following proof, mainly to
    point out several useful tactics and proof techniques.

    Starting a proof with "Proof with <some tactic>" allows us to
    specify a default tactic that should be used to solve goals.  To
    invoke this default tactic at the end of a proof step, we signal
    the end of the step with three periods instead of a single one,
    e.g., "apply typing_weakening...". *)

Proof with simpl_env;
           eauto 4 using wf_typ_strengthening,
                         wf_env_strengthening,
                         sub_strengthening.

  (** The proof proceeds by induction on the given typing derivation
      for e.  We use the [remember] tactic, along with [generalize
      dependent], to ensure that the goal is properly strengthened
      before we use induction. *)

  intros U E F x T e u TypT TypU.
  remember (F ++ x ~ bind_typ U ++ E) as E'.
  generalize dependent F.
  induction TypT; intros F EQ; subst; simpl subst_exp_in_exp...

  (** The [typing_var] case involves a case analysis on whether the
      variable is the same as the one being substituted for. *)

  Case "typing_var".
    destruct (x0 == x); try subst x0.

    (** In the case where [x0=x], we first observe that hypothesis
        [H0] implies that [T=U], since [x] can only be bound once in
        the environment.  The conclusion then follows from hypothesis
        [TypU] and weakening.  We can use the [analyze_binds_uniq]
        tactic, described in the MetatheoryEnv library, with [H0] to
        obtain the fact that [T=U]. *)

    SCase "x0 = x".
      analyze_binds_uniq H0.
        injection BindsTacVal; intros; subst.

        (** In order to apply [typing_weakening], we need to rewrite
            the environment so that it has the right shape.  (We could
            also prove a corollary of typing_weakening.)  The
            [rewrite_env] tactic, described in the Environment
            library, is one way to perform this rewriting. *)

        rewrite_env (empty ++ F ++ E).
        apply typing_weakening...

    (** In the case where [x0<>x], the result follows by an exhaustive
        case analysis on exactly where [x0] is bound in the
        environment.  We perform this case analysis by using the
        [analyze_binds] tactic, described in the MetatheoryEnv
        library. *)

    SCase "x0 <> x".
      analyze_binds H0.
        eauto using wf_env_strengthening.
        eauto using wf_env_strengthening.

  (** Informally, the [typing_abs] case is a straightforward
      application of the induction hypothesis, which is called [H0]
      here. *)

  Case "typing_abs".

    (** We use the "pick fresh and apply" tactic to apply the rule
        [typing_abs] without having to calculate the appropriate
        finite set of atoms. *)

    pick fresh y and apply typing_abs.

    (** We cannot apply [H0] directly here.  The first problem is that
        the induction hypothesis has [(subst_exp_in_exp open_exp_wrt_exp)], whereas in
        the goal we have [(open_exp_wrt_exp subst_exp_in_exp)].  The lemma
        [subst_exp_in_exp_open_exp_wrt_exp_var] lets us swap the order of these two
        operations. *)

    rewrite subst_exp_in_exp_open_exp_wrt_exp_var...

    (** The second problem is how the concatenations are associated in
        the environments.  In the goal, we currently have

<<       (y ~ bind_typ V ++ F ++ E),
>>
        where concatenation associates to the right.  In order to
        apply the induction hypothesis, we need

<<        ((y ~ bind_typ V ++ F) ++ E).
>>
        We can use the [rewrite_env] tactic to perform this rewriting,
        or we can rewrite directly with an appropriate lemma from the
        MetatheoryEnv library. *)

    rewrite <- app_assoc.

    (** Now we can apply the induction hypothesis. *)

    apply H0...

  (** The remaining cases in this proof are straightforward, given
      everything that we have pointed out above. *)

  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    rewrite subst_exp_in_exp_open_exp_wrt_typ_var...
    rewrite <- app_assoc.
    apply H0...
  Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var...
    rewrite <- app_assoc.
    apply H0...
  Case "typing_case".
    pick fresh y and apply typing_case...
      rewrite subst_exp_in_exp_open_exp_wrt_exp_var...
        rewrite <- app_assoc.
        apply H0...
      rewrite subst_exp_in_exp_open_exp_wrt_exp_var...
        rewrite <- app_assoc.
        apply H2...
Qed.
(* end show *)


(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

Lemma typing_through_subst_typ_in_exp : forall Q E F Z e T P,
  typing (F ++ Z ~ bind_sub Q ++ E) e T ->
  sub E P Q ->
  typing (map (subst_typ_in_binding P Z) F ++ E) (subst_typ_in_exp P Z e) (subst_typ_in_typ P Z T).
Proof with simpl_env;
           eauto 6 using wf_env_subst_typ_in_binding,
                         wf_typ_subst_typ_in_binding,
                         sub_through_subst_typ_in_typ.
  intros Q E F Z e T P Typ PsubQ.
  remember (F ++ Z ~ bind_sub Q ++ E) as G.
  generalize dependent F.
  induction Typ; intros F EQ; subst;
    simpl subst_typ_in_exp in *; simpl subst_typ_in_typ in *...
  Case "typing_var".
    apply typing_var...
      rewrite (map_subst_typ_in_binding_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      analyze_binds H0...
  Case "typing_abs".
    pick fresh y and apply typing_abs.
    rewrite subst_typ_in_exp_open_exp_wrt_exp_var...
    rewrite_env (map (subst_typ_in_binding P Z) (y ~ bind_typ T1 ++ F) ++ E).
    apply H0...
  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    rewrite subst_typ_in_exp_open_exp_wrt_typ_var...
    rewrite subst_typ_in_typ_open_typ_wrt_typ_var...
    rewrite_env (map (subst_typ_in_binding P Z) (Y ~ bind_sub T1 ++ F) ++ E).
    apply H0...
  Case "typing_tapp".
    rewrite subst_typ_in_typ_open_typ_wrt_typ...
  Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite subst_typ_in_exp_open_exp_wrt_exp_var...
    rewrite_env (map (subst_typ_in_binding P Z) (y ~ bind_typ T1 ++ F) ++ E).
    apply H0...
  Case "typing_case".
    pick fresh y and apply typing_case...
    SCase "inl branch".
      rewrite subst_typ_in_exp_open_exp_wrt_exp_var...
      rewrite_env (map (subst_typ_in_binding P Z) (y ~ bind_typ T1 ++ F) ++ E).
      apply H0...
    SCase "inr branch".
      rewrite subst_typ_in_exp_open_exp_wrt_exp_var...
      rewrite_env (map (subst_typ_in_binding P Z) (y ~ bind_typ T2 ++ F) ++ E).
      apply H2...
Qed.


(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)


(* ********************************************************************** *)
(** ** Inversion of typing (13) *)

Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (exp_abs S1 e1) T ->
  forall U1 U2, sub E T (typ_arrow U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall x, x `notin` L ->
     typing (x ~ bind_typ S1 ++ E) (open_exp_wrt_exp e1 (exp_var_f x)) S2 /\ sub E S2 U2.
Proof with auto.
  intros E S1 e1 T Typ.
  remember (exp_abs S1 e1) as e.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 b1 EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_abs".
    inversion Sub; subst.
    split...
    exists T2. exists L...
  Case "typing_sub".
    auto using (sub_transitivity T).
Qed.

Lemma typing_inv_tabs : forall E S1 e1 T,
  typing E (exp_tabs S1 e1) T ->
  forall U1 U2, sub E T (typ_all U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall X, X `notin` L ->
     typing (X ~ bind_sub U1 ++ E) (open_exp_wrt_typ e1 (typ_var_f X)) (open_typ_wrt_typ S2 (typ_var_f X))
     /\ sub (X ~ bind_sub U1 ++ E) (open_typ_wrt_typ S2 (typ_var_f X)) (open_typ_wrt_typ U2 (typ_var_f X)).
Proof with simpl_env; auto.
  intros E S1 e1 T Typ.
  remember (exp_tabs S1 e1) as e.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 e0 EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_tabs".
    inversion Sub; subst.
    split...
    exists T2.
    exists (L0 `union` L).
    intros Y Fr.
    split...
    rewrite_env (empty ++ Y ~ bind_sub U1 ++ E).
    apply (typing_narrowing S1)...
  Case "typing_sub".
    auto using (sub_transitivity T).
Qed.

Lemma typing_inv_inl : forall E e1 T,
  typing E (exp_inl e1) T ->
  forall U1 U2, sub E T (typ_sum U1 U2) ->
  exists S1, typing E e1 S1 /\ sub E S1 U1.
Proof with eauto.
  intros E e1 T Typ.
  remember (exp_inl e1) as e. generalize dependent e1.
  induction Typ; intros e' EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_sub".
    eauto using (sub_transitivity T).
  Case "typing_inl".
    inversion Sub; subst...
Qed.

Lemma typing_inv_inr : forall E e1 T,
  typing E (exp_inr e1) T ->
  forall U1 U2, sub E T (typ_sum U1 U2) ->
  exists S1, typing E e1 S1 /\ sub E S1 U2.
Proof with eauto.
  intros E e1 T Typ.
  remember (exp_inr e1) as e. generalize dependent e1.
  induction Typ; intros e' EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_sub".
    eauto using (sub_transitivity T).
  Case "typing_inr".
    inversion Sub; subst...
Qed.


(* ********************************************************************** *)
(** ** Preservation (20) *)

Lemma preservation : forall E e e' T,
  typing E e T ->
  red e e' ->
  typing E e' T.
Proof with simpl_env; eauto.
  intros E e e' T Typ. generalize dependent e'.
  induction Typ; intros e' Red; try solve [ inversion Red; subst; eauto ].
  Case "typing_app".
    inversion Red; subst...
    SCase "red_abs".
      destruct (typing_inv_abs _ _ _ _ Typ1 T1 T2) as [P1 [S2 [L P2]]].
        apply sub_reflexivity...
      pick fresh x.
      destruct (P2 x) as [? ?]...
      rewrite (subst_exp_in_exp_intro x)...
      rewrite_env (empty ++ E).
      apply (typing_through_subst_exp_in_exp T).
        apply typing_sub with (S := S2)...
          rewrite_env (empty ++ x ~ bind_typ T ++ E).
          apply sub_weakening...
        eauto.
  Case "typing_tapp".
    inversion Red; subst...
    SCase "red_tabs".
      destruct (typing_inv_tabs _ _ _ _ Typ T1 T2) as [P1 [S2 [L P2]]].
        apply sub_reflexivity...
      pick fresh X.
      destruct (P2 X) as [? ?]...
      rewrite (subst_typ_in_exp_intro X)...
      rewrite (subst_typ_in_typ_intro X)...
      rewrite_env (map (subst_typ_in_binding T X) empty ++ E).
      apply (typing_through_subst_typ_in_exp T1)...
  Case "typing_let".
    inversion Red; subst.
      SCase "red_let_1".
        eapply typing_let; eauto.
      SCase "red_let".
        pick fresh x.
        rewrite (subst_exp_in_exp_intro x)...
        rewrite_env (empty ++ E).
        apply (typing_through_subst_exp_in_exp T1)...
  Case "typing_case".
    inversion Red; subst.
    SCase "red_case_1".
      eapply typing_case; eauto.
    SCase "red_case_inl".
      destruct (typing_inv_inl _ _ _ Typ T1 T2) as [S1 [J2 J3]].
        apply sub_reflexivity...
      pick fresh x.
      rewrite (subst_exp_in_exp_intro x)...
      rewrite_env (empty ++ E).
      apply (typing_through_subst_exp_in_exp T1)...
    SCase "red_case_inr".
      destruct (typing_inv_inr _ _ _ Typ T1 T2) as [S1 [J2 J3]].
        apply sub_reflexivity...
      pick fresh x.
      rewrite (subst_exp_in_exp_intro x)...
      rewrite_env (empty ++ E).
      apply (typing_through_subst_exp_in_exp T2)...
Qed.


(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)


(* ********************************************************************** *)
(** ** Canonical forms (14) *)

Lemma canonical_form_abs : forall e U1 U2,
  is_value_of_exp e ->
  typing empty e (typ_arrow U1 U2) ->
  exists V, exists e1, e = exp_abs V e1.
Proof.
  intros e U1 U2 Val Typ.
  remember empty as E.
  remember (typ_arrow U1 U2) as T.
  revert U1 U2 HeqT HeqE.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion H0.
Qed.

Lemma canonical_form_tabs : forall e U1 U2,
  is_value_of_exp e ->
  typing empty e (typ_all U1 U2) ->
  exists V, exists e1, e = exp_tabs V e1.
Proof.
  intros e U1 U2 Val Typ.
  remember empty as E.
  remember (typ_all U1 U2) as T.
  revert U1 U2 HeqT HeqT.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion H0.
Qed.

Lemma canonical_form_sum : forall e T1 T2,
  is_value_of_exp e ->
  typing empty e (typ_sum T1 T2) ->
  exists e1, e = exp_inl e1 \/ e = exp_inr e1.
Proof.
  intros e T1 T2 Val Typ.
  remember empty as E.
  remember (typ_sum T1 T2) as T.
  revert T1 T2 HeqE HeqT.
  induction Typ; intros U1 U2 EQE EQT; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion H0.
Qed.


(* ********************************************************************** *)
(** ** Progress (16) *)

Lemma progress : forall e T,
  typing empty e T ->
  is_value_of_exp e \/ exists e', red e e'.
Proof with eauto.
  intros e T Typ.
  remember empty as E. generalize dependent HeqE.
  assert (Typ' : typing E e T)...
  induction Typ; intros EQ; simpl is_value_of_exp; subst...
  Case "typing_app".
    right.
    destruct IHTyp1 as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct IHTyp2 as [Val2 | [e2' Rede2']]...
      SSCase "Val2".
        destruct (canonical_form_abs _ _ _ Val1 Typ1) as [S [e3 EQ]].
        subst.
        assert (lc_exp (exp_abs S e3)) as J by auto; inversion J; subst.
        exists (open_exp_wrt_exp e3 e2)...
  Case "typing_tapp".
    right.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct (canonical_form_tabs _ _ _ Val1 Typ) as [S [e3 EQ]].
      subst.
      assert (lc_exp (exp_tabs S e3)) as J by auto; inversion J; subst.
      exists (open_exp_wrt_typ e3 T)...
  Case "typing_let".
    right.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
  Case "typing_inl".
    destruct (typing_inv_inl _ _ _ Typ' T1 T2) as [S1 [J2 J3]].
    apply sub_reflexivity...
    destruct IHTyp as [J1 | [e' J1]]...
  Case "typing_inr".
    destruct (typing_inv_inr _ _ _ Typ' T1 T2) as [S1 [J2 J3]].
    apply sub_reflexivity...
    destruct IHTyp as [J1 | [e' J1]]...
  Case "typing_case".
    right.
    destruct IHTyp as [Val1 | [e' Rede']]...
    SCase "Val1".
      destruct (canonical_form_sum _ _ _ Val1 Typ) as [e4 [J1 | J1]].
      SSCase "Left J1".
        subst.
        exists (open_exp_wrt_exp e2 e4).
        simpl in Val1.
        assert (lc_exp (exp_case (exp_inl e4) e2 e3)) by auto.
        inversion H3; subst.
        inversion H7; subst...
      SSCase "Right J1".
        subst.
        exists (open_exp_wrt_exp e3 e4)...
        simpl in Val1.
        assert (lc_exp (exp_case (exp_inr e4) e2 e3)) by auto.
        inversion H3; subst.
        inversion H7; subst...
Qed.
