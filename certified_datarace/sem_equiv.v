Require Export sem_inv.
Require Export Arith.

Module SemEquivProp (S1 S2:SEMANTIC).

Module I1 := SemInv S1.
Module I2 := SemInv S2.

Section equiv.

Variable p : program.
Variable pequiv : S1.C.pcontext -> S2.C.pcontext -> Prop.
Notation "x ~p y" := (pequiv x y) (at level 10).

Variable mequiv : S1.C.mcontext -> S2.C.mcontext -> Prop.
Notation "x ~m y" := (mequiv x y) (at level 10).

Inductive equiv_ppt : S1.PPT -> S2.PPT -> Prop :=
| equiv_ppt_def : forall m i c1 c2,
  c1 ~m c2 -> equiv_ppt (m,i,c1) (m,i,c2).
Notation "x ~ppt y" := (equiv_ppt x y) (at level 10).

Inductive equiv_memory_location : S1.memory_location -> S2.memory_location -> Prop :=
  | equiv_memory_location_def : forall l c1 c2,
    c1 ~p c2 -> equiv_memory_location (l,c1) (l,c2).
Notation "x ~ml y" := (equiv_memory_location x y) (at level 10).

Inductive equiv_memory_location' : S1.memory_location' -> S2.memory_location' -> Prop :=
| equiv_memory_location_def0 : forall l,
  equiv_memory_location' (l,None) (l,None)
| equiv_memory_location_def1 : forall l p1 p2,
  equiv_memory_location (l,p1) (l,p2) ->
  equiv_memory_location' (l,Some p1) (l,Some p2).
Notation "x ~ml' y" := (equiv_memory_location' x y) (at level 10).

Inductive equiv_val : S1.val -> S2.val -> Prop :=
| equiv_val_null : equiv_val S1.Null S2.Null
| equiv_val_loc : forall m1 m2, 
  m1 ~ml m2 -> equiv_val (S1.Loc m1) (S2.Loc m2).
Hint Constructors equiv_val.
Notation "x ~v y" := (equiv_val x y) (at level 10).

Definition equiv_local (l1:S1.local) (l2:S2.local) : Prop := 
  forall x, (l1 x) ~v (l2 x).
Notation "x ~l y" := (equiv_local x y) (at level 10).

Definition equiv_object (o1:field -> S1.val) (o2:field -> S2.val) : Prop := 
  forall f, (o1 f) ~v (o2 f).
Notation "x ~o y" := (equiv_object x y) (at level 10).

Inductive equiv_stack : S1.op_stack -> S2.op_stack -> Prop :=
| equiv_stack_nil : equiv_stack nil nil
| equiv_stack_cons : forall v1 v2 s1 s2,
  v1 ~v v2 -> equiv_stack s1 s2 -> equiv_stack (v1::s1) (v2::s2).
Notation "x ~s y" := (equiv_stack x y) (at level 10).

Inductive equiv_bot (A1 A2:Set) (equiv:A1->A2->Prop) : option A1 -> option A2 -> Prop :=
| equiv_bot_none : equiv_bot A1 A2 equiv None None
| equiv_bot_some : forall a1 a2, equiv a1 a2 -> equiv_bot A1 A2 equiv (Some a1) (Some a2).
Implicit Arguments equiv_bot [A1 A2].

Definition equiv_heap (h1:S1.heap) (h2:S2.heap) : Prop := 
  (forall m1, h1 m1 <> None ->
    exists m2, m1 ~ml m2 /\ equiv_bot equiv_object (h1 m1) (h2 m2))
  /\
  forall  a, S1.fresh h1 a -> S2.fresh h2 a.
Notation "x ~h y" := (equiv_heap x y) (at level 10).

Inductive equiv_frame : S1.frame -> S2.frame -> Prop :=
| equiv_frame_def : forall m i c1 c2 s1 s2 rho1 rho2,
  c1 ~m c2 -> s1 ~s s2 -> rho1 ~l rho2 ->
  equiv_frame (m,i,c1,s1,rho1) (m,i,c2,s2,rho2).
Notation "x ~f y" := (equiv_frame x y) (at level 10).

Inductive equiv_callstack : S1.call_stack -> S2.call_stack -> Prop :=
| equiv_callstack_nil : equiv_callstack nil nil
| equiv_callstack_cons : forall v1 v2 s1 s2,
  v1 ~f v2 -> equiv_callstack s1 s2 -> equiv_callstack (v1::s1) (v2::s2).
Notation "x ~cs y" := (equiv_callstack x y) (at level 10).

Definition equiv_threads (L1:S1.threads) (L2:S2.threads) : Prop := 
  (forall m1, L1 m1 <> None ->
    exists m2, m1 ~ml' m2 /\ equiv_bot equiv_callstack (L1 m1) (L2 m2))
  /\
  forall  a, (forall c, L1 (a,c) = None) -> (forall c, L2 (a,c) = None).
Notation "x ~t y" := (equiv_threads x y) (at level 10).

Inductive equiv_event : S1.event -> S2.event -> Prop :=
| equiv_event_def : forall k ppt1 ppt2 f, 
  ppt1 ~ppt ppt2 -> 
  equiv_event (k,ppt1,f) (k,ppt2,f).
Notation "x ~e y" := (equiv_event x y) (at level 10).

Inductive equiv_action : S1.action -> S2.action -> Prop :=
| equiv_action_none : equiv_action None None
| equiv_action_some : forall o1 e1 o1' o2 e2 o2',
  o1 ~ml' o2 -> e1 ~e e2 -> o1' ~ml o2' -> equiv_action (Some (o1,e1,o1')) (Some (o2,e2,o2')).
Notation "x ~a y" := (equiv_action x y) (at level 10).

Lemma equiv_subst : forall rho1 rho2 x v1 v2,
  v1 ~v v2 -> rho1 ~l rho2 -> (S1.subst rho1 x v1) ~l (S2.subst rho2 x v2).
Proof.
  intros.
  intros y; unfold S1.subst, S2.subst.
  comp x y; auto.
Qed.
Hint Resolve equiv_subst.

Lemma equiv_updatefield : forall o1 o2 f v1 v2,
  v1 ~v v2 -> o1 ~o o2 -> (S1.updateField o1 f v1) ~o (S2.updateField o2 f v2).
Proof.
  intros.
  intros y; unfold S1.updateField, S2.updateField.
  comp f y; auto.
Qed.
Hint Resolve equiv_updatefield.

Lemma read_equiv : forall sigma1 sigma2 o1 f v1 o2,
  sigma1 ~h sigma2 -> o1 ~ml o2 ->
  S1.read sigma1 o1 f v1 ->
  sigma2 o2 <> None ->
  S2.wf_heap sigma2 ->
  exists v2, S2.read sigma2 o2 f v2 /\ v1 ~v v2.
Proof.
  intros sigma1 sigma2 o1 f v1 o2 H H0 H1 V1 V2.
  destruct H1 as [o [H1 H2]].
  destruct H as [H _].
  destruct (H o1) as [o2' [T1 T2]]; try congruence.
  assert (o2'=o2).
  inv H0; inv T1.
  replace c2 with c3; auto.
  apply V2 with l; try congruence.
  rewrite H1 in T2; inv T2; congruence.
  subst.
  inv T2; try congruence.
  exists (a2 f); split.
  exists a2; split; auto.
  assert (o=a1) by congruence.
  subst; auto.
Qed.

Ltac MLcase2 x y := destruct (S2.eq_memloc x y); [subst|idtac].
Ltac MLcase1 x y := destruct (S1.eq_memloc x y); [subst|idtac].
Ltac MLcase2' x y := destruct (S2.eq_memloc' x y); [subst|idtac].
Ltac MLcase1' x y := destruct (S1.eq_memloc' x y); [subst|idtac].

Lemma exists_write : forall sigma l f v,
  sigma l <> None ->
  exists sigma', S2.write sigma l f v sigma'.
Proof.
  intros.
  case_eq (sigma l); intuition.
  set (o':=fun f0 => if eq_pos f f0 then v else v0 f0).
  exists (fun l0 => if S2.eq_memloc l l0 then Some o' else sigma l0).
  constructor.
  exists v0; split; auto.
  MLcase2 l l; intuition.
  intros.
  MLcase2 l l'; intuition.
Qed.

Lemma write_equiv : forall sigma1 sigma2 o1 f v1 v2 o2 sigma1',
  S1.wf_heap sigma1 ->
  S2.wf_heap sigma2 ->
  sigma1 ~h sigma2 -> o1 ~ml o2 -> v1 ~v v2 ->
  S1.write sigma1 o1 f v1 sigma1' ->
  sigma2 o2 <> None ->
  (forall o1 o1' o2, o1 ~ml o2 -> o1' ~ml o2 -> o1=o1') ->
  exists sigma2', 
    S2.write sigma2 o2 f v2 sigma2' /\ sigma1' ~h sigma2'.
Proof.
  intros sigma1 sigma2 o1 f v1 v2 o2 sigma1' Hwf1 Hwf2 H H0 H1 H2 V W.
  destruct H2.
  destruct H2 as [o [H2 H4]].
  elim exists_write with sigma2 o2 f v2.
  intros sigma2' T2.
  exists sigma2'; split; auto.
  split.
  intros m1 Hm1.
  destruct (excluded_middle (o1=m1)); subst.
  exists o2; split; auto.
  rewrite H4.
  destruct T2 as [[oo2 [T3 T4]] T2].
  rewrite T4; repeat constructor.
  apply equiv_updatefield; auto.
  destruct H as [H _].
  destruct (H m1) as [m2 [S1 S2]].
  congruence.
  assert (o2=m2).
  inv S1; inv H0.
  replace c2 with c3; auto.
  apply Hwf2 with l; try congruence.
  rewrite H2 in S2; inv S2; congruence.
  subst.
  rewrite H2 in S2; rewrite T3 in S2.
  inv S2; auto.
  rewrite H3; auto.
  rewrite H3 in Hm1; auto.
  destruct H as [H _].
  destruct (H m1) as [m2 [V1 V2]]; auto.
  destruct T2 as [[oo2 [T3 T4]] T2].
  exists m2; split; auto.
  rewrite T2; auto.
  intro; subst.
  elim H5; inv H0; inv V1.
  replace c1 with c0; auto.
  apply Hwf1 with l; congruence.
  repeat intro.
  destruct H as [H T].
  destruct o1 as [l1 c1].
  destruct o2 as [l2 c2].
  destruct (excluded_middle (a=l1)); subst.
  unfold S1.fresh in *.
  rewrite H5 in H4; congruence.
  inv H0; inv T2.
  rewrite H7; try congruence.
  apply T.
  intro.
  rewrite <- H3; auto.
  congruence.
  auto.
Qed.

Lemma alloc_equiv : forall sigma1 sigma2 o1 o2 sigma1',
  S1.wf_heap sigma1 ->
  S2.wf_heap sigma2 ->
  (forall o1 o1' o2, o1 ~ml o2 -> o1' ~ml o2 -> o1=o1') ->
  sigma1 ~h sigma2 -> o1 ~ml o2 -> 
  S1.alloc sigma1 o1 sigma1' ->
  S2.fresh sigma2 (fst o2) ->
  exists sigma2',
    S2.alloc sigma2 o2 sigma2' /\ sigma1' ~h sigma2'.
Proof.
  intros sigma1 sigma2 o1 o2 sigma1' Hwf1 Hwf2 Hf H H0 H1 T2.
  destruct H1 as [H1 [H2 H3]].
  exists (fun o => if S2.eq_memloc o o2 then Some (fun _ => S2.Null) else sigma2 o).
  repeat split; auto.
  destruct o2; auto.
  MLcase2 o2 o2; intuition.
  intros.
  MLcase2 l' o2; intuition.
  intros m1 Hm.
  MLcase1 m1 o1.
  rewrite H2.
  exists o2; split; auto.
  MLcase2 o2 o2; intuition.
  repeat constructor.
  rewrite H3; auto.
  rewrite H3 in Hm; auto.
  destruct H as [H _].
  destruct (H m1) as [m2 [S1 S2]]; auto.
  exists m2; split; auto.
  MLcase2 m2 o2; auto.
  elim n; eauto.
  repeat intro.
  destruct o1 as [l1 c1].
  destruct o2 as [l2 c2].
  inv H0.
  MLcase2 (a,c) (l2,c2).
  inv e.
  rewrite H4 in H2; congruence.
  destruct (excluded_middle (a=l2)); subst.
  apply T2; auto.
  destruct H.
  apply H5.
  intro.
  rewrite <- H3; auto.
  congruence.
Qed.

Lemma step0_equiv : forall o1 ppt1 o2 ppt2 a1 i ins rho1 rho2 s1 s2 s1' sigma1 sigma2 i' rho1' sigma1',
  S1.wf_heap sigma1 ->
  S2.wf_heap sigma2 ->
  (forall o1 o1' o2, o1 ~ml o2 -> o1' ~ml o2 -> o1=o1') ->
  (forall o, In (S2.Loc o) s2 -> sigma2 o <> None) ->
  o1 ~ml' o2 -> ppt1 ~ppt ppt2 -> s1 ~s s2 -> rho1 ~l rho2 -> sigma1 ~h sigma2 ->
  S1.step0 o1 ppt1 ins (i,s1,rho1,sigma1) (i',s1',rho1',sigma1') a1 ->
  exists a2, exists rho2', exists s2', exists sigma2',
  S2.step0 o2 ppt2 ins (i,s2,rho2,sigma2) (i',s2',rho2',sigma2') a2 /\
  a1 ~a a2 /\ s1' ~s s2' /\ rho1' ~l rho2' /\ sigma1' ~h sigma2'.
Proof.
  intros o1 ppt1 o2 ppt2 a1 i ins rho1 rho2 s1 s2 s1' sigma1 sigma2 i' rho1' sigma1' Hwf1 Hwf2 He Hinv Ho Hppt Hs H H0 H1.
  inv H1.
  (* AConstNull *)
  repeat (econstructor;eauto).
  (* ALoad *)
  repeat (econstructor;eauto).
  (* Astore *)
  inv Hs.
  repeat (econstructor;eauto).
  (* GetField *)
  inv Hs.
  inv H3.
  elim read_equiv with (1:=H0) (2:=H2) (3:=HYP2); auto.
  intros v2 [T1 T2].
  exists (Some (o2,(Get,ppt2,f),m2)).
  exists rho2.
  exists (v2::s0).
  repeat (econstructor;eauto).
  auto with datatypes.
  (* Putfield *)
  inv Hs.
  inv H5.
  inv H4.
  elim write_equiv with (3:=H0) (4:=H2) (5:=H3) (6:=HYP2); auto.
  intros sigma2' [S1 S2].
  exists (Some (o2,(Put,ppt2,f),m2)).
  repeat (econstructor;eauto).
  auto with datatypes.
  (* ifnd *)
  repeat (econstructor;eauto).
  repeat (econstructor;eauto).
  (* goto *)
  repeat (econstructor;eauto).
Qed.

Lemma step1_equiv : forall m m' o1 o2 a1 i rho1 rho2 s1 s2 s1' sigma1 sigma2 i' rho1' sigma1' c1 c2 c1',
  S1.wf_heap sigma1 ->
  S2.wf_heap sigma2 ->
  (forall o1 o1' o2, o1 ~ml o2 -> o1' ~ml o2 -> o1=o1') ->
  (forall o, In (S2.Loc o) s2 -> sigma2 o <> None) ->
  (forall m i cid c1 c2, c1 ~m c2 -> body m i = Some (New cid) ->
    (S1.C.make_new_context m i cid c1) ~p (S2.C.make_new_context m i cid c2)) ->
  c1 ~m c2 -> o1 ~ml' o2 -> s1 ~s s2 -> rho1 ~l rho2 -> sigma1 ~h sigma2 ->
  S1.step1 o1 (m,i,c1,s1,rho1,sigma1) (m',i',c1',s1',rho1',sigma1') a1 ->
  exists a2, exists c2', exists rho2', exists s2', exists sigma2',
  S2.step1 o2 (m,i,c2,s2,rho2,sigma2) (m',i',c2',s2',rho2',sigma2') a2 /\
  c1' ~m c2' /\ a1 ~a a2 /\ s1' ~s s2' /\ rho1' ~l rho2' /\ sigma1' ~h sigma2'.
Proof.
  intros m m' o1 o2 a1 i rho1 rho2 s1 s2 s1' sigma1 sigma2 i' rho1' sigma1' c1 c2 c1'.
  intros Hwf1 Hwf2 He Hinv He2 Hc Ho Hs H H0 H1.
  inv H1.
  (* step0 *)
  elim step0_equiv with (5:=Ho) (ppt2:=(m',i,c2)) (7:=Hs) (8:=H) (9:=H0) (10:=HYP2); auto.
  intros a2 [rho2' [s2' [sigma2' T]]].
  decompose [and] T.
  repeat (econstructor;eauto).
  constructor; auto.
  (* New *)
  elim (alloc_equiv sigma1 sigma2 (a, S1.C.make_new_context m' i cid c1') (a, S2.C.make_new_context m' i cid c2) sigma1'); auto.
  intros sigma2' [S1 S2].
  exists (None:S2.action).
  exists c2.
  exists rho2.
  exists (S2.Loc (a, S2.C.make_new_context m' i cid c2) :: s2).
  exists sigma2'; repeat (split; auto).
  constructor 2; auto.
  destruct H0; auto.
  constructor.
  repeat constructor; auto.
  constructor; apply He2; auto.  
  destruct H0; simpl; auto.
Qed.

Lemma equiv_app : forall s1_1 s1_2 s2,
  (s1_1++s1_2) ~s s2 -> 
  exists s2_1, exists s2_2, s2 = s2_1++s2_2 /\ s1_1 ~s s2_1 /\ s1_2 ~s s2_2.
Proof.
  induction s1_1; simpl; intros.
  exists (nil:S2.op_stack); exists s2; repeat split; auto.
  constructor.
  inv H.
  elim IHs1_1 with (1:=H4); auto.
  intros s2_1 [s2_2 [T1 [T2 T3]]].
  exists (v2::s2_1); exists s2_2; repeat split; auto.
  rewrite T1; auto.
  constructor; auto.
Qed.

Lemma equiv_stack_length : forall s1 s2,
  s1 ~s s2 -> length s1 = length s2.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma equiv_stack_nth : forall s1 s2,
  s1 ~s s2 -> 
  forall x, (nth x s1 S1.Null) ~v (nth x s2 S2.Null).
Proof.
  induction 1; destruct x; simpl; auto.
Qed.

Lemma step2_equiv : forall o1 o2 sigma1 sigma2 sigma1' cs1 cs2 cs1' a1,
  S1.wf_heap sigma1 ->
  S2.wf_heap sigma2 ->
  (forall o1 o1' o2, o1 ~ml o2 -> o1' ~ml o2 -> o1=o1') ->
  (forall o1 o2, o1 ~p o2 -> S1.C.get_class p o1 = S2.C.get_class p o2) ->
  (forall f, In f cs2 ->
    match f with (_,_,_,s,_) => forall o, In (S2.Loc o) s -> sigma2 o <> None end) ->
  (forall m i cid c1 c2, c1 ~m c2 -> body m i = Some (New cid) ->
    (S1.C.make_new_context m i cid c1) ~p (S2.C.make_new_context m i cid c2)) ->
  (forall m i c1 c2 p1 p2, c1 ~m c2 -> p1 ~p p2 ->
    (S1.C.make_call_context m i c1 p1) ~m (S2.C.make_call_context m i c2 p2)) ->
  o1 ~ml' o2 -> cs1 ~cs cs2 -> sigma1 ~h sigma2 ->
  S1.step2 p o1 (cs1,sigma1) (cs1',sigma1') a1 ->
  exists a2, exists cs2', exists sigma2',
  S2.step2 p o2 (cs2,sigma2) (cs2',sigma2') a2 /\
  a1 ~a a2 /\ cs1' ~cs cs2' /\ sigma1' ~h sigma2'.
Proof.
  intros o1 o2 sigma1 sigma2 sigma1' cs1 cs2 cs1' a1 Hwf1 Hwf2 He Hec Hinv He1 He2 Ho Hcs Hh Hs.
  inv Hs.
  (* step1 *)
  inv Hcs.
  inv H1.
  assert (Hi:=Hinv (m, i, c2, s0, rho2)); simpl in Hi; clear Hinv. 
  destruct fr' as [[[[m' i'] c1'] s1'] rho1'].
  elim step1_equiv with m m' o1 o2 a1 i rho1 rho2 s1 s0 s1' sigma1 sigma2 i' rho1' sigma1' c1 c2 c1'; auto.
  intros a2 [c2' [rho2' [s2' [sigma2' T]]]].
  decompose [and] T.
  exists a2; exists ((m',i',c2',s2',rho2')::s2).
  repeat (econstructor; eauto).
  (* invokevirtual *)
  inv Hcs.
  inv H1.
  clear Hinv.
  exists (None:S2.action).
  elim equiv_app with (1:=H15).
  intros v_list2 [ss2 T].
  decompose [and] T; subst; clear T.
  inv H2.
  inv H6.
  set (rho2':=fun x =>
        if eq_var x 0 then S2.Loc m2 
          else if le_gt_dec x (length args) then nth (length args - x) v_list2 S2.Null
            else S2.Null).
  exists ((m1, 0, S2.C.make_call_context m i c2 (snd m2), nil, rho2')
        :: (m, S i, c2, s0, rho2) :: s2).
  exists sigma2.
  split.
  econstructor; eauto.
  rewrite <- (Hec (snd o')); auto.
  inv H0; simpl; auto.
  unfold rho2'.
  destruct (eq_var 0 0); intuition.
  intros; unfold rho2'.
  destruct (eq_var x 0); try (apply False_ind; omega).
  destruct (le_gt_dec x (length args)).
  auto.
  apply False_ind; omega.
  intros; unfold rho2'.
  destruct (eq_var x 0); try (apply False_ind; omega).
  destruct (le_gt_dec x (length args)).
  apply False_ind; omega.
  auto.
  assert (L:=equiv_stack_length _ _ H1).
  congruence.
  repeat (constructor; auto).
  apply He2; auto.
  inv H0; auto.
  unfold rho2'; intros z.
  destruct (eq_var z 0).
  subst; rewrite H9.
  constructor; auto.
  destruct (le_gt_dec z (length args)).
  rewrite H10; auto.
  apply equiv_stack_nth; auto.
  unfold var in *; omega.
  rewrite H11; auto.
  (* return *)
  exists (None:S2.action).
  inv Hcs.
  inv H1.
  exists s2.
  exists sigma2.
  repeat (constructor; auto).
  (* Areturn *)
  exists (None:S2.action).
  inv Hcs.
  inv H1.
  inv H9.
  inv H3.
  inv H2.
  exists ((m',i',c0,v2::s2,rho0)::s0).
  exists sigma2.
  repeat (constructor; auto).
Qed.

Lemma equiv_upd_thread : forall L1 L2 o1 o2 cs1 cs2,
  (forall o1 o1' o2, o1 ~ml o2 -> o1' ~ml o2 -> o1=o1') ->
  L1 ~t L2 -> o1 ~ml' o2 -> cs1 ~cs cs2 ->
  (S1.upd_thread L1 o1 cs1) ~t (S2.upd_thread L2 o2 cs2).
Proof.
  intros L1 L2 o1 o2 cs1 cs2 He H H0 H1.
  unfold S1.upd_thread, S2.upd_thread; split; intros.
  MLcase1' o1 m1.
  exists o2.
  split; auto.
  MLcase2' o2 o2; intuition.
  constructor; auto.
  destruct H.
  elim (H m1); auto.
  intros m2 [T1 T2].
  exists m2; split; auto.
  MLcase2' o2 m2; auto.
  elim n; eauto.
  inv T1; inv H0; try congruence.
  assert ((l,p0)=(l,p1)).
  eapply He; eauto.
  congruence.
  
  MLcase2' o2 (a,c).
  inv H0.
  generalize (H2 None).
  destruct S1.eq_memloc'; subst; intuition; discriminate.
  generalize (H2 (Some p1)).
  destruct S1.eq_memloc'; subst; intuition; discriminate.
  destruct H.
  apply H3.
  intros.  
  generalize (H2 c0).
  destruct S1.eq_memloc'; subst; intros; try discriminate.
  auto.
Qed.

Lemma step3_equiv : forall o1 o2 sigma1 sigma2 sigma1' cs1 cs2 mu mu' L1 L2 L1' a1,
  S1.wf_heap sigma1 ->
  S2.wf_heap sigma2 ->
  (forall o1 o1' o2, o1 ~ml o2 -> o1' ~ml o2 -> o1=o1') ->
  (forall o1 o2, o1 ~p o2 -> S1.C.get_class p o1 = S2.C.get_class p o2) ->
  (forall f, In f cs2 ->
    match f with (_,_,_,s,_) => forall o, In (S2.Loc o) s -> sigma2 o <> None end) ->
  (forall m i cid c1 c2, c1 ~m c2 -> body m i = Some (New cid) ->
    (S1.C.make_new_context m i cid c1) ~p (S2.C.make_new_context m i cid c2)) ->
  (forall m i c1 c2 p1 p2, c1 ~m c2 -> p1 ~p p2 ->
    (S1.C.make_call_context m i c1 p1) ~m (S2.C.make_call_context m i c2 p2)) ->
  L1 ~t L2 -> o1 ~ml' o2 -> cs1 ~cs cs2 -> sigma1 ~h sigma2 -> 
  S1.step3 p L1 (o1,cs1,sigma1,mu) (L1',sigma1',mu') a1 ->
  exists a2, exists L2', exists sigma2', 
  S2.step3 p L2 (o2,cs2,sigma2,mu) (L2',sigma2',mu') a2 /\
  L1' ~t L2' /\ a1 ~a a2 /\ sigma1' ~h sigma2'.
Proof.
  intros o1 o2 sigma1 sigma2 sigma1' cs1 cs2 mu mu' L1 L2 L1' a1 Hwf1 Hwf2 He1 He2 He3.
  intros He4 He5 H6 H7 H8 H10 H11.
  inv H11.
  (* step2 *)
  elim step2_equiv with o1 o2 sigma1 sigma2 sigma1' cs1 cs2 cs' a1; auto.
  intros a2 [cs2' [sigma2' [T1 [T2 [T3 T4]]]]].
  exists a2.
  exists (S2.upd_thread L2 o2 cs2').
  exists sigma2'.
  split.
  constructor 1; auto.
  split; auto.
  apply equiv_upd_thread; auto.
  (* run *)
  inv H8.
  inv H1.
  clear He3.
  inv H11.
  inv H1.
  exists None.
  set (rho2':=fun x =>
        if eq_var x 0 then S2.Loc m2 
          else S2.Null).
  exists ( (S2.upd_thread
            (S2.upd_thread L2 o2 ((m, S2.next_line i, c2, s3, rho2) :: s2)) (fst m2,Some (snd m2))
            ((m1, 0, S2.C.make_call_context m i c2 (snd m2), nil, rho2') :: nil))).
  exists sigma2.
  split.
  econstructor 2; eauto.
  inv H0; simpl in *.
  rewrite <- (He2 _ _ H); auto.
  unfold rho2'.
  destruct (eq_var 0 0); intuition.
  unfold rho2'.
  intros x.
  destruct (eq_var (S x) 0); auto.
  congruence.
  inv H0; simpl in *.
  destruct H6; auto.
  split.
  apply equiv_upd_thread; auto.
  apply equiv_upd_thread; auto.
  repeat (constructor;auto).
  inv H0; simpl; constructor; auto.
  repeat (constructor;auto).
  repeat (constructor;auto).
  apply He5; auto.
  inv H0; auto.
  unfold rho2'; intros z.
  destruct (eq_var z 0).
  subst; rewrite H17; constructor; auto.
  destruct z; intuition.
  rewrite H18; constructor.
  split.
  repeat (constructor;auto).
  auto.
  (* MonitorEnter *)
  inv H8.
  inv H1.
  inv H11.
  inv H1.
  clear He3.
  exists None.
  exists (S2.upd_thread L2 o2 ((m, S2.next_line i, c2, s3, rho2) :: s2)).
  exists sigma2.
  split.
  econstructor 3; eauto.
  inv H0; inv H7; simpl in *; auto.
  split.
  apply equiv_upd_thread; auto.
  repeat (constructor; auto).
  split; auto.
  repeat (constructor; auto).
  (* MonitorExit *)
  inv H8.
  inv H1.
  inv H11.
  inv H1.
  clear He3.
  exists None.
  exists (S2.upd_thread L2 o2 ((m, S2.next_line i, c2, s3, rho2) :: s2)).
  exists sigma2.
  split.
  econstructor 4; eauto.
  inv H0; inv H7; simpl in *; auto.
  split.
  apply equiv_upd_thread; auto.
  repeat (constructor; auto).
  split; auto.
  repeat (constructor; auto).
Qed.

Lemma step_equiv : forall sigma1 sigma2 sigma1' mu mu' L1 L2 L1' a1,
  S1.wf_heap sigma1 ->
  S2.wf_heap sigma2 ->
  (forall o1 o1' o2, o1 ~ml o2 -> o1' ~ml o2 -> o1=o1') ->
  (forall o1 o2, o1 ~p o2 -> S1.C.get_class p o1 = S2.C.get_class p o2) ->
  (forall o cs f, L2 o = Some cs -> In f cs ->
    match f with (_,_,_,s,_) => forall o, In (S2.Loc o) s -> sigma2 o <> None end) ->
  (forall m i cid c1 c2, c1 ~m c2 -> body m i = Some (New cid) ->
    (S1.C.make_new_context m i cid c1) ~p (S2.C.make_new_context m i cid c2)) ->
  (forall m i c1 c2 p1 p2, c1 ~m c2 -> p1 ~p p2 ->
    (S1.C.make_call_context m i c1 p1) ~m (S2.C.make_call_context m i c2 p2)) ->
  L1 ~t L2 -> sigma1 ~h sigma2 -> 
  S1.step p (L1,sigma1,mu) (L1',sigma1',mu') a1 ->
  exists a2, exists L2', exists sigma2', 
  S2.step p (L2,sigma2,mu) (L2',sigma2',mu') a2 /\
  L1' ~t L2' /\ a1 ~a a2 /\ sigma1' ~h sigma2'.
Proof.
  intros sigma1 sigma2 sigma1' mu mu' L1 L2 L1' a1 Hwf1 Hwf2 He1 He2 He3 H6 H7 H8 H9 H10.
  inv H10.
  elim H8; intros.
  elim (H o); try congruence.
  intros o2 [V1 V2].
  rewrite H12 in V2; inv V2.
  inv H3.
  elim step3_equiv with o o2 sigma1 sigma2 sigma1' (fr::cs) (v2::s2) mu mu' L1 L2 L1' a1; auto.
  intros a2 [L2' [sigma2' T]].
  decompose [and] T; clear T.
  exists a2; exists L2'; exists sigma2'.
  split.
  repeat (econstructor; eauto).
  auto.
  intros.
  eapply He3; eauto.
  constructor; auto.
Qed.

Lemma init_equiv : 
  S1.C.init_pcontext ~p S2.C.init_pcontext ->
  S1.C.init_mcontext ~m S2.C.init_mcontext ->
  (forall m i cid c1 c2, c1 ~m c2 -> body m i = Some (New cid) ->
    (S1.C.make_new_context m i cid c1) ~p (S2.C.make_new_context m i cid c2)) ->
  match S1.init p, S2.init p with
    | (L1,sigma1,mu1), (L2,sigma2,mu2) =>
      L1 ~t L2 /\ sigma1 ~h sigma2 /\ mu1=mu2
  end.
Proof.
  intros; unfold S1.init, S2.init.
  repeat split; auto; intros.
  unfold S1.threads_init in *.
  destruct S1.eq_memloc'; simpl.
  exists (S2.run_address, None); subst.
  split.
  constructor.
  unfold S2.threads_init.
  destruct S2.eq_memloc'; simpl.
  repeat constructor.
  auto.
  intuition.
  intuition.  
  unfold S1.threads_init, S2.threads_init in *.
  destruct S2.eq_memloc'; simpl; auto.
  inv e.
  generalize (H2 None).
  destruct S1.eq_memloc'; simpl; intros.
  discriminate.
  elim n; auto.
  unfold S1.sigma_init, S2.sigma_init in *.
  destruct S1.eq_memloc; simpl; intuition.
  exists (S2.run_address, S2.init_p p); intuition.
  subst; constructor; auto.
  unfold S1.init_p, S2.init_p.
  apply H1.
  auto.
  apply foo_prop.
  MLcase2 (S2.run_address, S2.init_p p) (S2.run_address, S2.init_p p); intuition.
  repeat constructor.
  unfold S1.fresh, S2.fresh in *.
  unfold S1.sigma_init, S2.sigma_init in *.
  intros.
  MLcase2 (a, c) (S2.run_address, S2.init_p p); auto.
  inv e.
  generalize (H2 (S1.init_p p)); intros.
  MLcase1 (S2.run_address, S1.init_p p) (S1.run_address, S1.init_p p).
  discriminate.
  elim n; auto.
Qed.

Lemma reach_equiv : 
  S1.C.init_pcontext ~p S2.C.init_pcontext ->
  S1.C.init_mcontext ~m S2.C.init_mcontext ->
  (forall o1 o1' o2, o1 ~ml o2 -> o1' ~ml o2 -> o1=o1') ->
  (forall o1 o2, o1 ~p o2 -> S1.C.get_class p o1 = S2.C.get_class p o2) ->
  (forall m i cid c1 c2, c1 ~m c2 -> body m i = Some (New cid) ->
    (S1.C.make_new_context m i cid c1) ~p (S2.C.make_new_context m i cid c2)) ->
  (forall m i c1 c2 p1 p2, c1 ~m c2 -> p1 ~p p2 ->
    (S1.C.make_call_context m i c1 p1) ~m (S2.C.make_call_context m i c2 p2)) ->
  forall st, 
    S1.reachable p st ->
    match st with (L1,sigma1,mu) =>
      exists L2, exists sigma2, 
        S2.reachable p (L2,sigma2,mu) /\ L1 ~t L2 /\ sigma1 ~h sigma2
    end.
Proof.
  intros until st.
  induction 1.
  generalize (S2.reachable_0 p).
  case_eq (S2.init p); intros Ls mu2.
  destruct Ls as [L2 sigma2].
  unfold S1.init.
  intros.
  replace ((fun _:location => Free):S2.lock) with mu2 in *.
  intros; exists L2; exists sigma2; split; auto.
  generalize (init_equiv H H0).
  rewrite H5; unfold S1.init.
  intuition.
  unfold S2.init in *.
  congruence.
  destruct st as [[L sigma]mu].
  destruct IHreachable as [L2 [sigma2 [B [B1 B2]]]].
  auto.
  destruct st' as [[L' sigma']mu'].
  elim step_equiv with (L2:=L2) (sigma2:=sigma2) (10:=H'); auto.
  intros a2 [L2' [sigma2' T]].
  decompose [and] T.
  exists L2'; exists sigma2'; split; intuition.
  constructor 2 with (L2,sigma2,mu) a2; auto.
  generalize (I1.reachable_wf_heap _ _ H5); auto.
  generalize (I2.reachable_wf_heap _ _ B); auto.
  intros.
  destruct (I2.reachable_wf _ _ B _ _ H6).
  destruct f as [[[[m i] c] s] rho].
  assert (I:=H8 _ H7).
  inv I.
  auto.
Qed.

Lemma step2_some_dom_sigma : forall p L sigma mu st' o e o',
  S2.step p (L, sigma, mu) st' (Some (o, e, o')) ->
  sigma o' <> None.
Proof.
  intros.
  inv H.
  inv H5.
  inv H10.
  inv H7.
  inv HYP2.
  inv HYP3; intuition; congruence.
  inv HYP3.
  destruct H; intuition; congruence.
Qed.

Lemma race_equiv : 
  S1.C.init_pcontext ~p S2.C.init_pcontext ->
  S1.C.init_mcontext ~m S2.C.init_mcontext ->
  (forall o1 o1' o2, o1 ~ml o2 -> o1' ~ml o2 -> o1=o1') ->
  (forall o1 o2, o1 ~p o2 -> S1.C.get_class p o1 = S2.C.get_class p o2) ->
  (forall m i cid c1 c2, c1 ~m c2 -> body m i = Some (New cid) ->
    (S1.C.make_new_context m i cid c1) ~p (S2.C.make_new_context m i cid c2)) ->
  (forall m i c1 c2 p1 p2, c1 ~m c2 -> p1 ~p p2 ->
    (S1.C.make_call_context m i c1 p1) ~m (S2.C.make_call_context m i c2 p2)) ->
  forall ppt ppt',
    S1.race_without_context p ppt ppt' -> S2.race_without_context p ppt ppt'.
Proof.
  intros.
  inv H5.
  destruct st as [[L1 sigma1]mu].
  assert (exists L2, exists sigma2, 
    S2.reachable p (L2,sigma2,mu) /\ L1 ~t L2 /\ sigma1 ~h sigma2).
  apply reach_equiv with (7:=H6); auto.
  destruct H5 as [L2 [sigma2 [T1 [T2 T3]]]].
  destruct st1 as [[L1' sigma1']mu'].
  elim step_equiv with (L2:=L2) (sigma2:=sigma2) (10:=H7); auto.
  intros a2' [L2' [sigma2' T]].
  decompose [and] T; clear T.
  inv H12; try (inv H11; fail).
  destruct st2 as [[L1'' sigma1'']mu''].
  elim step_equiv with (L2:=L2) (sigma2:=sigma2) (10:=H8); auto.
  intros a2'' [L2'' [sigma2'' T']].
  decompose [and] T'; clear T'.
  inv H18; try (inv H11; fail).
  inv H10; inv H9; inv H11.
  inv H16; inv H22.
  inv H25; inv H24.
  constructor 1 with (1:=T1) (2:=H5) (3:=H12) (c1:=c3) (c2:=c4); auto.
  econstructor.
  econstructor.
  assert (o2'=o2'0).
  inv H23; inv H17.
  replace c7 with c5; auto.
  assert (S2.wf_heap sigma2).
  generalize (I2.reachable_wf_heap _ _ T1); auto.
  apply (H10 l).
  eapply step2_some_dom_sigma; eauto.
  eapply step2_some_dom_sigma; eauto.
  subst.
  constructor; auto.
  assert (forall o1 o1' o2, o1 ~ml' o2 -> o1' ~ml' o2 -> o1=o1').
  intros.
  inv H9; inv H10; auto.
  replace p1 with p0; auto.
  assert ((l,p1)=(l,p0)) by eauto; congruence.
  intro; subst.
  elim H18; eauto.
  generalize (I1.reachable_wf_heap _ _ H6); auto.
  generalize (I2.reachable_wf_heap _ _ T1); auto.
  intros.
  destruct (I2.reachable_wf _ _ T1 _ _ H12).
  destruct f as [[[[m i] c] s] rho].
  assert (I:=H19 _ H18).
  inv I.
  auto.
  generalize (I1.reachable_wf_heap _ _ H6); auto.
  generalize (I2.reachable_wf_heap _ _ T1); auto.
  intros.
  destruct (I2.reachable_wf _ _ T1 _ _ H5).
  destruct f as [[[[m i] c] s] rho].
  assert (I:=H13 _ H12).
  inv I.
  auto.
Qed.

End equiv.

End SemEquivProp.
