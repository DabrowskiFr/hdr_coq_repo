Require Export counting_semantic_inv.
Require Export sem_inv.

Module CountingSemanticEquiv (S1:SEMANTIC) (S2:COUNTING_SEMANTIC with Module C:=S1.C).

  Import S1.C.
  Module Inv := CountingSemanticInv S2. Import Inv.
  Module I1 := SemInv S1.

Section equiv.
  Variable p : program.

  Inductive equiv_memory_location : S1.memory_location -> S2.memory_location -> Prop :=
  | equiv_memory_location_def : forall l c m i om pi cid,
    body m i = Some (New cid) ->
    equiv_memory_location (l,make_new_context m i cid c) (l,CP m i c om pi).
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
    (forall m2, h2 m2 <> None ->
      exists m1, m1 ~ml m2 /\ equiv_bot equiv_object (h1 m1) (h2 m2))
    /\
    forall  a, S1.fresh h1 a <-> S2.fresh h2 a.
  Notation "x ~h y" := (equiv_heap x y) (at level 10).

  Inductive equiv_frame : S1.frame -> S2.frame -> Prop :=
  | equiv_frame_def : forall m i c s1 s2 rho1 rho2 om pi,
    s1 ~s s2 -> rho1 ~l rho2 ->
    equiv_frame (m,i,c,s1,rho1) (CP m i c om pi,s2,rho2).
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
    (forall m2, L2 m2 <> None ->
      exists m1, m1 ~ml' m2 /\ equiv_bot equiv_callstack (L1 m1) (L2 m2))
    /\
    forall  a, (forall c, L1 (a,c) = None) <-> (forall c, L2 (a,c) = None).
  Notation "x ~t y" := (equiv_threads x y) (at level 10).

  Inductive equiv_state : S1.state -> S2.state -> Prop :=
    equiv_state_def : forall L1 L2 omg mu sigma1 sigma2,
      L1 ~t L2 -> sigma1 ~h sigma2 -> equiv_state (L1,sigma1,mu) (L2,sigma2,mu,omg).

  Inductive equiv_action : S1.action -> S2.action -> Prop :=
  | equiv_action_none : equiv_action None None
  | equiv_action_some : forall o1  o1' o2 o2' e,
    o1 ~ml' o2 -> o1' ~ml o2' -> equiv_action (Some (o1,e,o1')) (Some (o2,e,o2')).
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

Lemma He : forall o1 o1' o2, o1 ~ml o2 -> o1' ~ml o2 -> o1=o1'.
Proof.
  intros.
  inv H; inv H0; try congruence.
Qed.

Lemma He' : forall o1 o1' o2, o1 ~ml' o2 -> o1' ~ml' o2 -> o1=o1'.
Proof.
  intros.
  inv H; inv H0; try congruence.
  assert ((l,p1)=(l,p0)).
  eapply He; eauto.
  congruence.
Qed.

Lemma read_equiv : forall sigma1 sigma2 o1 f v1 o2,
  sigma1 ~h sigma2 -> o1 ~ml o2 ->
  S1.read sigma1 o1 f v1 ->
  sigma2 o2 <> None ->
  wf sigma2 ->
  exists v2, S2.read sigma2 o2 f v2 /\ v1 ~v v2.
Proof.
  intros sigma1 sigma2 o1 f v1 o2 H H0 H1 V1 V2.
  destruct H1 as [o [H1 H2]].
  destruct H as [H _].
  destruct (H o1) as [o2' [T1 T2]]; try congruence.
  assert (o2'=o2).
  rewrite H1 in T2; inv T2.  
  inv H0; inv T1.
  replace (CP m0 i0 c0 om0 pi0) with (CP m i c om pi); auto.
  apply V2 with l; try congruence.
  apply V1.
  unfold location, S2.code_pointer in *.
  congruence.
  subst.
  rewrite H1 in T2; inv T2.
  exists (a2 f).
  split; auto.
  exists a2; split; auto.
Qed.

Lemma wf_aux : forall sigma o o1 o2,
  wf sigma -> sigma o1 <> None -> sigma o2 <> None ->
  o ~ml o1 -> o ~ml o2 -> o1=o2.
Proof.
  intros.
  inv H2; inv H3; simpl in *.
  replace (CP m i c om pi) with (CP m0 i0 c0 om0 pi0); auto.
  eauto.
Qed.

Lemma wf_aux' : forall sigma o o1 o2,
  wf sigma -> wf_h sigma o1 -> wf_h sigma o2 ->
  o ~ml' o1 -> o ~ml' o2 -> o1=o2.
Proof.
  intros.
  inv H2; inv H3; simpl in *.
  auto.
  assert ((l,p2)=(l,p3)).
  eapply wf_aux; eauto.
  congruence.
Qed.

Lemma wf_aux1 : forall sigma o o1 o2,
  S1.wf_heap sigma -> sigma o1 <> None -> sigma o2 <> None ->
  o1 ~ml o -> o2 ~ml o -> o1=o2.
Proof.
  intros.
  inv H2; inv H3; simpl in *.
  replace (make_new_context m i cid c) with (make_new_context m i cid0 c); auto.
  eauto.
Qed.

Lemma read_equiv2 : forall sigma1 sigma2 o1 f v2 o2,
  sigma1 ~h sigma2 -> o1 ~ml o2 ->
  S2.read sigma2 o2 f v2 ->
  sigma1 o1 <> None ->
  S1.wf_heap sigma1 ->
  exists v1, S1.read sigma1 o1 f v1 /\ v1 ~v v2.
Proof.
  intros sigma1 sigma2 o1 f v2 o2 H H0 H1 V1 V2.
  destruct H1 as [o [H1 H2]].
  destruct H as [_ [H _]].
  destruct (H o2) as [o1' [T1 T2]]; try congruence.
  rewrite H1 in T2; inv T2.
  assert (o1'=o1) by (eapply wf_aux1; eauto; congruence).
  subst.
  exists (a1 f).
  split; auto.
  exists a1; split; auto.
Qed.

Ltac Case x y := destruct (excluded_middle (x=y)); [subst|idtac].
Ltac MLcase1 x y := destruct (S1.eq_memloc x y); [subst|idtac].
Ltac MLcase2 x y := destruct (S2.eq_memloc x y); [subst|idtac].
Ltac MLcase1' x y := destruct (S1.eq_memloc' x y); [subst|idtac].
Ltac MLcase2' x y := destruct (S2.eq_memloc' x y); [subst|idtac].

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
  wf sigma2 ->
  sigma1 ~h sigma2 -> o1 ~ml o2 -> v1 ~v v2 ->
  S1.write sigma1 o1 f v1 sigma1' ->
  sigma2 o2 <> None ->
  True ->
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
  assert (CP m0 i0 c0 om0 pi0=CP m i c om pi).
  apply Hwf2 with l; try congruence.
  unfold location, S2.code_pointer in *.
  rewrite H2 in S2; inv S2; congruence.
  unfold location, S2.code_pointer in *.
  rewrite H2 in S2; inv S2; congruence.
  inv H0; auto.
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
  assert (cid=cid0) by congruence; subst; auto.
  split.
  intros m2 Hm2.
  inv T2.
  destruct H5 as [mm2 [M1 M2]].
  destruct (excluded_middle (o2=m2)); subst.
  exists o1; split; auto.
  rewrite M2.
  rewrite H4.
  constructor.
  apply equiv_updatefield; auto.
  destruct H as [H _].
  elim H with o1; try congruence; clear H.
  intros m2' [V1 V2].
  rewrite H2 in V2; inv V2.
  assert (m2=m2') by (eapply wf_aux; eauto; try congruence).
  subst.
  replace mm2 with a2 by congruence; auto.
  rewrite H6 in Hm2; auto.
  destruct H as [_ [H _]].
  elim H with m2; try congruence.
  intros m1 [V1 V2].
  exists m1; split; auto.
  rewrite H6; auto.
  rewrite H3; auto.
  intro; subst.
  assert (o2=m2) by (eapply wf_aux; eauto; try congruence).
  intuition.
  
  destruct H as [H [H' T]].
  destruct o1 as [l1 c1].
  destruct o2 as [l2 c2].
  inv T2.
  unfold S1.fresh, S2.fresh, S2.inDom in *; intros; split; intros.
  destruct (excluded_middle (a=l1)); subst.
  rewrite H7 in H4; congruence.
  inv H0.
  rewrite H6; try congruence.
  destruct (T a).
  apply H0; intros.
  generalize (H7 c0); rewrite H3; try congruence.
  destruct (excluded_middle (a=l2)); subst.
  destruct H5 as [m2 [V1 V2]].
  elim (H7 c2); try congruence.
  inv H0.
  rewrite H3; try congruence.
  destruct (T a).
  apply H9.
  intros.
  rewrite <- H6; try congruence.
  eauto.
  auto.
Qed.

Lemma exists_write1 : forall sigma l f v,
  sigma l <> None ->
  exists sigma', S1.write sigma l f v sigma'.
Proof.
  intros.
  case_eq (sigma l); intuition.
  set (o':=fun f0 => if eq_pos f f0 then v else v0 f0).
  exists (fun l0 => if S1.eq_memloc l l0 then Some o' else sigma l0).
  constructor.
  exists v0; split; auto.
  MLcase1 l l; intuition.
  intros.
  MLcase1 l l'; intuition.
Qed.

Lemma write_equiv2 : forall sigma1 sigma2 o1 f v1 v2 o2 sigma2',
  S1.wf_heap sigma1 ->
  wf sigma2 ->
  sigma1 ~h sigma2 -> o1 ~ml o2 -> v1 ~v v2 ->
  S2.write sigma2 o2 f v2 sigma2' ->
  sigma1 o1 <> None ->
  exists sigma1', 
    S1.write sigma1 o1 f v1 sigma1' /\ sigma1' ~h sigma2'.
Proof.
  intros sigma1 sigma2 o1 f v1 v2 o2 sigma2' Hwf1 Hwf2 H H0 H1 H2 V.
  destruct H2.
  destruct H2 as [o [H2 H4]].
  elim exists_write1 with sigma1 o1 f v1.
  intros sigma1' T2.
  exists sigma1'; split; auto.
  split.
  intros m1 Hm1.
  destruct T2 as [[oo2 [T3 T4]] T2].
  destruct (excluded_middle (o1=m1)); subst.
  exists o2; split; auto.
  rewrite H4.
  rewrite T4; repeat constructor.
  apply equiv_updatefield; auto.
  destruct H as [H _].
  destruct (H m1) as [m2 [S1 S2]].
  congruence.
  rewrite T3 in S2; inv S2.
  assert (o2=m2) by (eapply wf_aux; eauto; congruence).
  subst.
  replace a2 with o in * by congruence; auto.
  destruct H as [H _].
  rewrite T2 in Hm1; auto.
  rewrite T2; auto.
  elim H with (1:=Hm1).
  intros m2 [V1 V2].
  exists m2; split; auto.
  rewrite H3; auto.
  intro; subst.
  elim H5; eapply wf_aux1; eauto; congruence.
  split.
  intros m2 Hm2.
  destruct T2 as [[oo2 [T3 T4]] T2].
  destruct (excluded_middle (o2=m2)); subst.
  exists o1; split; auto.
  rewrite H4.
  rewrite T4; repeat constructor.
  apply equiv_updatefield; auto.
  destruct H as [_ [H _]].
  destruct (H m2) as [m1 [S1 S2]].
  congruence.
  rewrite H2 in S2; inv S2.
  assert (o1=m1) by (eapply wf_aux1; eauto; congruence).
  subst.
  replace a1 with oo2 in * by congruence; auto.
  destruct H as [_ [H _]].
  rewrite H3 in Hm2; auto.
  rewrite H3; auto.
  elim H with (1:=Hm2).
  intros m1 [V1 V2].
  exists m1; split; auto.
  rewrite T2; auto.
  intro; subst.
  elim H5; eapply wf_aux; eauto; congruence.
  
  destruct H as [H [H' T]].
  destruct o1 as [l1 c1].
  destruct o2 as [l2 c2].
  inv T2.
  destruct H5 as [m1 [M1 M2]].
  unfold S1.fresh, S2.fresh, S2.inDom in *; intros; split; intros.
  destruct (excluded_middle (a=l1)); subst.
  rewrite H5 in M2; congruence.
  rewrite H3.
  destruct (T a) as [T0 _]; apply T0.
  intros; rewrite <- H6; auto; congruence.
  inv H0; congruence.
  destruct (excluded_middle (a=l2)); subst.
  elim (H5 c2); congruence.
  rewrite H6.
  destruct (T a) as [_ T0]; apply T0.
  intros; rewrite <- H3; try congruence.
  eauto.
  inv H0; congruence.
  auto.
Qed.

Lemma alloc_equiv : forall sigma1 sigma2 o1 o2 sigma1',
  S1.wf_heap sigma1 ->
  wf sigma2 ->
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
  unfold S2.fresh, S2.inDom in *; destruct o2; simpl in *.
  generalize (T2 c); destruct (sigma2 (l,c)); intuition congruence.
  MLcase2 o2 o2; intuition.
  intros.
  MLcase2 l' o2; intuition.
  intros m1 Hm.
  Case m1 o1.
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
  elim H4; eauto.
  intros m2.
  MLcase2 m2 o2; intros.
  exists o1; rewrite H2; split; auto.
  repeat constructor.
  destruct H as [_ [H _]].
  destruct (H _ H4) as [m1 [M1 M2]].
  exists m1; split; auto.
  rewrite H3; auto.
  intro; subst.
  rewrite H1 in M2; inv M2; congruence.
  destruct H as [_ [_ H]].
  simpl in *; unfold S2.fresh, S1.fresh, S2.inDom in *; intros.
  destruct (excluded_middle (a=fst o2)); subst.
  destruct o2 as [l2 p2]; simpl in *.
  MLcase (l2, p0) (l2, p2).
  inv e; inv H0; rewrite H4 in H2; congruence.
  auto.
  MLcase2 (a, p0) o2.
  elim H5; auto.
  destruct  (H a).
  apply H6; intros.
  rewrite <- H3; auto.
  inv H0; simpl in *; congruence.
  destruct H as [_ [_ H]].
  simpl in *; unfold S2.fresh, S1.fresh, S2.inDom in *; intros.
  destruct (excluded_middle (a=fst o1)); subst.
  destruct o1 as [l p1]; simpl in *.
  elim (H4 (snd o2)).  
  inv H0; simpl in *.
  destruct (S2.eq_memloc (@pair location S2.code_pointer l
               (@CP mcontext S2.mVect S2.lVect m i c0 om pi))
            (@pair location (cp mcontext S2.mVect S2.lVect) l
               (@CP mcontext S2.mVect S2.lVect m i c0 om pi))).
  congruence.
  intuition.
  rewrite H3.
  destruct (H a).
  apply H7; intros.
  generalize (H4 p0).
  MLcase2 (a,p0) o2; auto.
  destruct o1; simpl in *.
  congruence.
Qed.

Lemma alloc_equiv2 : forall sigma1 sigma2 o1 o2 sigma2',
  S1.wf_heap sigma1 ->
  wf sigma2 ->
  sigma1 ~h sigma2 -> o1 ~ml o2 -> 
  S2.alloc sigma2 o2 sigma2' ->
  S1.fresh sigma1 (fst o1) ->
  exists sigma1',
    S1.alloc sigma1 o1 sigma1' /\ sigma1' ~h sigma2'.
Proof.
  intros sigma1 sigma2 o1 o2 sigma2' Hwf1 Hwf2 Hf H H1 T.
  destruct H1 as [H1 [H2 H3]].
  exists (fun o => if S1.eq_memloc o o1 then Some (fun _ => S1.Null) else sigma1 o).
  split.
  repeat split; auto.
  destruct o1; auto.
  MLcase1 o1 o1; intuition.
  intros.
  MLcase1 l' o1; intuition.
  repeat split; intros.
  MLcase1 m1 o1.
  exists o2; split; auto.
  rewrite H2; repeat constructor.
  destruct Hf.
  elim H4 with m1; auto.
  intros m2 [M1 M2].
  exists m2; split; auto.
  rewrite H3; auto.
  intro; subst.
  rewrite H1 in M2; inv M2; congruence.
  MLcase2 m2 o2.
  exists o1; split; auto.
  MLcase1 o1 o1.
  rewrite H2; repeat constructor.
  intuition.
  rewrite H3 in H0; auto.
  destruct Hf as [_ [Hf _]].
  destruct (Hf _ H0) as [m1 [M1 M2]].
  exists m1; split; auto.
  MLcase1 m1 o1.
  destruct o1; simpl in *; rewrite T in M2.
  inv M2; congruence.
  rewrite H3; auto.
  simpl in *; unfold S2.fresh, S1.fresh, S2.inDom in *; intros.
  destruct (excluded_middle (a=fst o2)); subst.  
  generalize (H0 (snd o1)).
  inv H; simpl in *.
  destruct (S1.eq_memloc (l, make_new_context m i cid c) (l, make_new_context m i cid c)).
  congruence.
  intuition.
  rewrite H3.
  destruct Hf as [_ [_ Hf]].
  destruct (Hf a).
  simpl in *; unfold S2.fresh, S1.fresh, S2.inDom in *; intros.
  apply H5; intros.
  generalize (H0 c).
  MLcase1 (a,c) o1; try congruence.
  destruct o2; simpl in *; congruence.
  simpl in *; unfold S2.fresh, S1.fresh, S2.inDom in *; intros.
  destruct (excluded_middle (a=fst o1)); subst.  
  destruct o1 as [l p1]; simpl in *.
  elim H0 with (snd o2).
  inv H; simpl in *.
  unfold S2.code_pointer.
  rewrite H2; congruence.
  MLcase1 (a,c) o1.
  elim H0 with (snd o2).
  inv H; simpl in *.
  unfold S2.code_pointer.
  rewrite H2; congruence.
  destruct Hf as [_ [_ Hf]].
  destruct (Hf a).
  apply H6.
  intro.
  unfold S2.inDom.
  rewrite <- H3; eauto.
  inv H; simpl in *; congruence.
Qed.


Lemma step0_equiv : forall o1 ppt o2 a1 i ins rho1 rho2 s1 s2 s1' sigma1 sigma2 i' rho1' sigma1',
  S1.wf_heap sigma1 ->
  wf sigma2 ->
  (forall o, In (S2.Loc o) s2 -> sigma2 o <> None) ->
  o1 ~ml' o2 -> s1 ~s s2 -> rho1 ~l rho2 -> sigma1 ~h sigma2 ->
  S1.step0 o1 ppt ins (i,s1,rho1,sigma1) (i',s1',rho1',sigma1') a1 ->
  exists a2, exists rho2', exists s2', exists sigma2',
  S2.step0 o2 ppt ins (i,s2,rho2,sigma2) (i',s2',rho2',sigma2') a2 /\
  a1 ~a a2 /\ s1' ~s s2' /\ rho1' ~l rho2' /\ sigma1' ~h sigma2'.
Proof.
  intros o1 ppt o2 a1 i ins rho1 rho2 s1 s2 s1' sigma1 sigma2 i' rho1' sigma1' Hwf1 Hwf2 Hinv Ho Hs H H0 H1.
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
  exists (Some (o2,(Get,ppt,f),m2)).
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
  exists (Some (o2,(Put,ppt,f),m2)).
  repeat (econstructor;eauto).
  auto with datatypes.
  (* ifnd *)
  repeat (econstructor;eauto).
  repeat (econstructor;eauto).
  (* goto *)
  repeat (econstructor;eauto).
Qed.

Lemma step0_equiv2 : forall o1 ppt o2 a2 i ins rho1 rho2 s1 s2 s2' sigma1 sigma2 i' rho2' sigma2',
  S1.wf_heap sigma1 ->
  wf sigma2 ->
  (forall o, In (S1.Loc o) s1 -> sigma1 o <> None) ->
  o1 ~ml' o2 -> s1 ~s s2 -> rho1 ~l rho2 -> sigma1 ~h sigma2 ->
  S2.step0 o2 ppt ins (i,s2,rho2,sigma2) (i',s2',rho2',sigma2') a2 ->
  exists a1, exists rho1', exists s1', exists sigma1',
  S1.step0 o1 ppt ins (i,s1,rho1,sigma1) (i',s1',rho1',sigma1') a1 /\
  a1 ~a a2 /\ s1' ~s s2' /\ rho1' ~l rho2' /\ sigma1' ~h sigma2'.
Proof.
  intros o1 ppt o2 a1 i ins rho1 rho2 s1 s2 s2' sigma1 sigma2 i' rho2' sigma2' Hwf1 Hwf2 Hinv Ho Hs H H0 H1.
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
  inv H4.
  elim read_equiv2 with (1:=H0) (2:=H3) (3:=HYP2); auto.
  intros v2 [T1 T2].
  exists (Some (o1,(Get,ppt,f),m1)).
  exists rho1.
  exists (v2::s0).
  repeat (econstructor;eauto).
  auto with datatypes.
  (* Putfield *)
  inv Hs.
  inv H5.
  inv H6.
  elim write_equiv2 with (3:=H0) (4:=H3) (5:=H4) (6:=HYP2); auto.
  intros sigma1' [S1 S2].
  exists (Some (o1,(Put,ppt,f),m1)).
  repeat (econstructor;eauto).
  auto with datatypes.
  (* ifnd *)
  repeat (econstructor;eauto).
  repeat (econstructor;eauto).
  (* goto *)
  repeat (econstructor;eauto).
Qed.

Lemma step1_equiv : forall m m' o1 o2 a1 i rho1 rho2 s1 s2 s1' sigma1 sigma2 i' rho1' sigma1' c c' om pi,
  S1.wf_heap sigma1 ->
  wf sigma2 ->
  (forall o, In (S2.Loc o) s2 -> sigma2 o <> None) ->
  o1 ~ml' o2 -> s1 ~s s2 -> rho1 ~l rho2 -> sigma1 ~h sigma2 ->
  S1.step1 o1 (m,i,c,s1,rho1,sigma1) (m',i',c',s1',rho1',sigma1') a1 ->
  exists a2, exists rho2', exists s2', exists sigma2', exists om', exists pi', 
  S2.step1 o2 (CP m i c om pi,s2,rho2,sigma2) (CP m' i' c' om' pi',s2',rho2',sigma2') a2 /\
  a1 ~a a2 /\ s1' ~s s2' /\ rho1' ~l rho2' /\ sigma1' ~h sigma2'.
Proof.
  intros m m' o1 o2 a1 i rho1 rho2 s1 s2 s1' sigma1 sigma2 i' rho1' sigma1' c c' om pi.
  intros Hwf1 Hwf2 Hinv Ho Hs H H0 H1.
  inv H1.
  (* step0 *)
  elim step0_equiv with (4:=Ho) (5:=Hs) (6:=H) (7:=H0) (8:=HYP2); auto.
  intros a2 [rho2' [s2' [sigma2' T]]].
  decompose [and] T.
  repeat (econstructor;eauto).
  (* New *)
  elim (alloc_equiv sigma1 sigma2 (a, make_new_context m' i cid c') (a,CP m' i c' om pi) sigma1'); auto.
  intros sigma2' [S1 S2].
  exists (None:S2.action).
  exists rho2.
  exists (S2.Loc (a, CP m' i c' om pi) :: s2).
  exists sigma2'; repeat (split; auto).
  exists om.
  exists (S2.incr_lVect pi m' c' (i,S2.next_line i)).
  split.
  econstructor 2; eauto.
  destruct H0 as [_ [ _ H0]].
  destruct (H0 a); auto.
  split.
  constructor.
  split.
  repeat constructor; auto.
  split; auto.
  apply He.
  constructor; auto.
  destruct H0; simpl; auto.
  destruct H1  as [ _ H1].
  destruct (H1 a); auto.
Qed.

Lemma step1_equiv2 : forall m m' o1 o2 a2 i rho1 rho2 s1 s2 s2' sigma1 sigma2 i' rho2' sigma2' c c' om pi om' pi',
  S1.wf_heap sigma1 ->
  wf sigma2 ->
  (forall o, In (S1.Loc o) s1 -> sigma1 o <> None) ->
  o1 ~ml' o2 -> s1 ~s s2 -> rho1 ~l rho2 -> sigma1 ~h sigma2 ->
  S2.step1 o2 (CP m i c om pi,s2,rho2,sigma2) (CP m' i' c' om' pi',s2',rho2',sigma2') a2 ->
  exists a1, exists rho1', exists s1', exists sigma1', 
  S1.step1 o1 (m,i,c,s1,rho1,sigma1) (m',i',c',s1',rho1',sigma1') a1 /\
  a1 ~a a2 /\ s1' ~s s2' /\ rho1' ~l rho2' /\ sigma1' ~h sigma2'.
Proof.
  intros m m' o1 o2 a2 i rho1 rho2 s1 s2 s2' sigma1 sigma2 i' rho2' sigma2' c c' om pi om' pi'.
  intros Hwf1 Hwf2 Hinv Ho Hs H H0 H1.
  inv H1.
  (* step0 *)
  elim step0_equiv2 with (4:=Ho) (5:=Hs) (6:=H) (7:=H0) (8:=HYP2); auto.
  intros a1 [rho1' [s1' [sigma1' T]]].
  decompose [and] T.
  repeat (econstructor;eauto).
  (* New *)
  elim (alloc_equiv2 sigma1 sigma2 (a, make_new_context m' i cid c') (a,CP m' i c' om' pi) sigma2'); auto.
  intros sigma1' [S1 S2].
  exists (None:S1.action).
  exists rho1.
  exists (S1.Loc (a, make_new_context m' i cid c') :: s1).
  exists sigma1'; repeat (split; auto).
  econstructor 2; eauto.
  destruct H0 as [_ [_ H0]].
  destruct (H0 a); auto.
  constructor.
  repeat constructor; auto.
  constructor; auto.
  destruct H0 as [_ [ _ H0]]; simpl.
  destruct (H0 a); auto.
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

Lemma step2_equiv : forall o1 o2 sigma1 sigma2 sigma1' cs1 cs2 cs1' a1 omg,
  S1.wf_heap sigma1 ->
  wf sigma2 ->
  (forall f, In f cs2 ->
    match f with (_,s,_) => forall o, In (S2.Loc o) s -> sigma2 o <> None end) ->
  o1 ~ml' o2 -> cs1 ~cs cs2 -> sigma1 ~h sigma2 ->
  S1.step2 p o1 (cs1,sigma1) (cs1',sigma1') a1 ->
  exists a2, exists cs2', exists sigma2', exists omg',
  S2.step2 p o2 (cs2,sigma2,omg) (cs2',sigma2',omg') a2 /\
  a1 ~a a2 /\ cs1' ~cs cs2' /\ sigma1' ~h sigma2'.
Proof.
  intros o1 o2 sigma1 sigma2 sigma1' cs1 cs2 cs1' a1 omg Hwf1 Hwf2 Hinv Ho Hcs Hh Hs.
  inv Hs.
  (* step1 *)
  inv Hcs.
  inv H1.
  assert (Hi:=Hinv (CP m i c om pi, s0, rho2)); simpl in Hi; clear Hinv. 
  destruct fr' as [[[[m' i'] c1'] s1'] rho1'].
  elim step1_equiv with m m' o1 o2 a1 i rho1 rho2 s1 s0 s1' sigma1 sigma2 i' rho1' sigma1' c c1' om pi; auto.
  intros a2 [rho2' [s2' [sigma2' [om' [pi' T]]]]].
  decompose [and] T.
  exists a2; exists ((CP m' i' c1' om' pi',s2',rho2')::s2).
  repeat (econstructor; eauto).
  (* invokevirtual *)
  inv Hcs.
  inv H1.
  clear Hinv.
  exists (None:S2.action).
  elim equiv_app with (1:=H14).
  intros v_list2 [ss2 T].
  decompose [and] T; subst; clear T.
  inv H2.
  inv H6.
  inv H0.
  set (c1:=S2.C.make_call_context m i c (make_new_context m0 i0 cid0 c0)).
  set (om1:=S2.invoke_mVect om m1 c1 omg).
  set (pi':=S2.incr_lVect pi m c (i,S i)).
  set (pi1:=S2.invoke_lVect pi' m1 c1).
  exists ((CP m1 0 c1 om1 pi1,nil,S2.local_of_list (S2.Loc (l, CP m0 i0 c0 om0 pi0)) v_list2)::(CP m (S i) c om pi',s0,rho2) :: s2).
  exists sigma2.
  exists (S2.incr_mVect omg m1 c1).
  split.
  simpl in H5.
  rewrite class_make_new_context in H5; auto.
  inv H5.
  econstructor 2; eauto.
  rewrite H2; auto.
  generalize (equiv_stack_length _ _ H1).
  congruence.
  repeat (constructor; auto).
  intros x; unfold S2.local_of_list.
  destruct x.
  rewrite H9; simpl.
  repeat constructor; auto.
  assert (length args=length v_list2) by
    (generalize (equiv_stack_length _ _ H1); congruence).
  rewrite <- H0 in *.
  destruct (le_gt_dec (S x) (length args)).
  rewrite H10; try omega.
  apply equiv_stack_nth; auto.
  rewrite H11; try omega; constructor.
  (* return *)
  exists (None:S2.action).
  inv Hcs.
  inv H1.
  exists s2.
  exists sigma2.
  exists omg.
  repeat (constructor; auto).
  (* Areturn *)
  exists (None:S2.action).
  inv Hcs.
  inv H1.
  inv H8.
  inv H3.
  inv H2.
  exists ((CP m' i' c' om0 pi0,v2::s2,rho0)::s0).
  exists sigma2.
  exists omg.
  repeat (constructor; auto).
Qed.

Lemma equiv_app2 : forall s1_1 s1_2 s2,
  s2 ~s (s1_1++s1_2) -> 
  exists s2_1, exists s2_2, s2 = s2_1++s2_2 /\ s2_1 ~s s1_1 /\ s2_2 ~s s1_2.
Proof.
  induction s1_1; simpl; intros.
  exists (nil:S1.op_stack); exists s2; repeat split; auto.
  constructor.
  inv H.
  elim IHs1_1 with (1:=H4); auto.
  intros s2_1 [s2_2 [T1 [T2 T3]]].
  exists (v1::s2_1); exists s2_2; repeat split; auto.
  rewrite T1; auto.
  constructor; auto.
Qed.

Lemma step2_equiv2 : forall o1 o2 sigma1 sigma2 sigma2' cs1 cs2 cs2' a2 omg omg',
  S1.wf_heap sigma1 ->
  wf sigma2 ->
  (forall f, In f cs1 ->
    match f with (_,_,_,s,_) => forall o, In (S1.Loc o) s -> sigma1 o <> None end) ->
  o1 ~ml' o2 -> cs1 ~cs cs2 -> sigma1 ~h sigma2 ->
  S2.step2 p o2 (cs2,sigma2,omg) (cs2',sigma2',omg') a2 ->
  exists a1, exists cs1', exists sigma1', 
  S1.step2 p o1 (cs1,sigma1) (cs1',sigma1') a1 /\
  a1 ~a a2 /\ cs1' ~cs cs2' /\ sigma1' ~h sigma2'.
Proof.
  intros o1 o2 sigma1 sigma2 sigma2' cs1 cs2 cs2' a2 omg omg' Hwf1 Hwf2 Hinv Ho Hcs Hh Hs.
  inv Hs.
  (* step1 *)
  inv Hcs.
  inv H2.
  assert (Hi:=Hinv (m,i,c, s0, rho1)); simpl in Hi; clear Hinv. 
  destruct fr' as [[[m' i' c2' om' pi'] s2'] rho2'].
  elim step1_equiv2 with (4:=Ho) (5:=H) (6:=H0) (7:=Hh) (8:=H7); auto.
  intros a1 [rho1' [s1' [sigma1' T]]].
  decompose [and] T.
  exists a1; exists ((m',i',c2',s1',rho1')::s1).
  repeat (econstructor; eauto).
  (* invokevirtual *)
  inv Hcs.
  inv H2.
  clear Hinv.
  exists (None:S1.action).
  elim equiv_app2 with (1:=H4).
  intros v_list1 [ss1 T].
  decompose [and] T; subst; clear T.
  inv H2.
  inv H7.
  inv H2.
  set (c1:=S1.C.make_call_context m i c (make_new_context m0 i0 cId c0)).
  set (rho1':=fun x => match x with
                        | 0 => S1.Loc (a0, make_new_context m0 i0 cid c0)
                        | _ => 
                          if le_gt_dec x (length args) 
                            then List.nth (length args -x) v_list1 S1.Null 
                            else S1.Null
                      end).                            
                          
  exists ((m1,0,c1,nil, rho1')::(m,S i,c,s0,rho1) :: s1).
  exists sigma1.
  split.
  econstructor 2; eauto.
  simpl.
  replace cid with cId.
  apply class_make_new_context; auto.
  congruence.
  replace cid with cId by congruence.
  auto.
  unfold rho1'; intros.
  destruct x.
  apply False_ind; omega.
  destruct (le_gt_dec (S x) (length args)).
  auto.
  apply False_ind; omega.
  unfold rho1'; intros.
  destruct x.
  apply False_ind; omega.
  destruct (le_gt_dec (S x) (length args)).
  apply False_ind; omega.
  auto.
  generalize (equiv_stack_length _ _ H1); congruence.
  repeat constructor.
  unfold rho1', S2.local_of_list; intro x.
  destruct x.
  repeat constructor; auto.
  assert (length args=length v_list) by
    (generalize (equiv_stack_length _ _ H1); congruence).
  rewrite H in *.
  destruct (le_gt_dec (S x) (length v_list)).
  apply equiv_stack_nth; auto.
  constructor.
  auto.
  auto.
  auto.
  destruct Hh; intuition.
  destruct Hh; intuition.
  destruct Hh as [_ [_ Hf]]; destruct (Hf a); auto.
  destruct Hh as [_ [_ Hf]]; destruct (Hf a); auto.
  (* return *)
  exists (None:S1.action).
  inv Hcs.
  inv H2.
  exists s1.
  exists sigma1.
  repeat (constructor; auto).
  (* Areturn *)
  exists (None:S1.action).
  inv Hcs.
  inv H2.
  inv H4.
  inv H3.
  inv H4.
  exists ((m0,i0,c0,v1::s1,rho0)::s0).
  exists sigma1.  
  repeat (constructor; auto).
Qed.

Lemma equiv_upd_thread : forall L1 L2 o1 o2 cs1 cs2 sigma2 omg,
  wf sigma2 -> wf' L2 sigma2 omg ->
  wf_h sigma2 o2 ->
  L1 ~t L2 -> o1 ~ml' o2 -> cs1 ~cs cs2 ->
  (S1.upd_thread L1 o1 cs1) ~t (S2.upd_thread L2 o2 cs2).
Proof.
  intros L1 L2 o1 o2 cs1 cs2 sigma2 omg W1 W2 W3 H H0 H1.
  unfold S1.upd_thread, S2.upd_thread; split; intros.
  destruct (S1.eq_memloc' o1 m1); subst.
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
  eapply He'; eauto.
  split.
  intros.
  destruct (S2.eq_memloc' o2 m2); subst.
  exists o1.
  split; auto.
  MLcase1' o1 o1; intuition.
  constructor; auto.
  destruct H as [ _ [H _]].
  elim (H m2); auto.
  intros m1 [T1 T2].
  exists m1; split; auto.
  MLcase1' o1 m1; auto.
  elim n; eauto.
  case_eq (L2 m2); intros.  
  destruct (W2 _ _ H3).
  eapply wf_aux'; eauto.
  intuition.

  split; intros.
  MLcase2' o2 (a,c).
  generalize (H2 (snd o1)).
  destruct o1 as [l1 p1]; simpl in *.
  MLcase1' (l1, p1) (a, p1).
  congruence.
  inv H0; congruence.
  destruct H as [_ [_ H]].
  destruct (H a).
  apply H3; intros.
  generalize (H2 c0).
  MLcase1' o1 (a,c0); auto.
  congruence.
  MLcase1' o1 (a,c).
  generalize (H2 (snd o2)).
  destruct o2 as [l2 p2]; simpl in *.
  MLcase2' (l2, p2) (a, p2).
  congruence.
  inv H0; congruence.
  destruct H as [_ [_ H]].
  destruct (H a).
  apply H4; intros.
  generalize (H2 c0).
  MLcase2' o2 (a,c0); auto.
  congruence.
Qed.

Lemma step3_equiv : forall o1 o2 sigma1 sigma2 sigma1' cs1 cs2 mu mu' L1 L2 L1' a1 omg,
  S1.wf_heap sigma1 ->
  wf sigma2 ->
  wf' L2 sigma2 omg -> L2 o2 = Some cs2 ->
  (forall f, In f cs2 ->
    match f with (_,s,_) => forall o, In (S2.Loc o) s -> sigma2 o <> None end) ->
  L1 ~t L2 -> o1 ~ml' o2 -> cs1 ~cs cs2 -> sigma1 ~h sigma2 -> 
  S1.step3 p L1 (o1,cs1,sigma1,mu) (L1',sigma1',mu') a1 ->
  exists a2, exists L2', exists sigma2',  exists omg',
  S2.step3 p L2 (o2,cs2,sigma2,mu,omg) (L2',sigma2',mu',omg') a2 /\
  L1' ~t L2' /\ a1 ~a a2 /\ sigma1' ~h sigma2'.
Proof.
  intros o1 o2 sigma1 sigma2 sigma1' cs1 cs2 mu mu' L1 L2 L1' a1 omg Hwf1 Hwf2 Hwf3 HL.
  intros He5 H6 H7 H8 H10 H11.
  inv H11.
  (* step2 *)
  elim step2_equiv with o1 o2 sigma1 sigma2 sigma1' cs1 cs2 cs' a1 omg; auto.
  intros a2 [cs2' [sigma2' [omg' [T1 [T2 [T3 T4]]]]]].
  exists a2.
  exists (S2.upd_thread L2 o2 cs2').
  exists sigma2'.
  exists omg'.
  split.
  constructor 1; auto.
  split; auto.
  eapply equiv_upd_thread with (omg:=omg); eauto.
  destruct (Hwf3 _ _ HL); auto.
  (* run *)
  inv H8.
  inv H1.
  inv H9.
  inv H1.
  exists (None).
  set (rho2':=fun x =>
        if eq_var x 0 then S2.Loc m2 
          else S2.Null).
  set (rho1':=S2.local_of_list (S2.Loc m2) nil).
  inv H0.
  set (c1:=make_call_context m i c (make_new_context m0 i0 cid0 c0)).
  set (om1:=S2.invoke_mVect S2.MVect.init m1 c1 omg).
  set (pi1:=S2.LVect.init).
  set (pi':=S2.incr_lVect pi m c (i,S i)).
  set (o:=(l, CP m0 i0 c0 om0 pi0)).
  exists ((S2.upd_thread 
              (S2.upd_thread L2 o2 ((CP m (S2.next_line i) c om pi',s3,rho2)::s2))
              (fst o, Some (snd o)) ((CP m1 0 c1 om1 pi1,nil,rho1')::nil))).
  exists sigma2.
  exists (S2.incr_mVect omg m1 c1).
  split.
  econstructor 2; unfold o in *; eauto.
  simpl in H13; rewrite class_make_new_context in H13.
  inv H13.
  rewrite H1 in *.
  auto.
  auto.
  destruct H6.
  destruct H1; auto.
  destruct (H2 l); auto.
  split.
  eapply equiv_upd_thread with (omg:=omg); eauto.
  repeat intro.
  unfold S2.upd_thread in *.
  MLcase2' o2 o0.
  destruct (Hwf3 _ _ HL); auto.
  split; auto.
  inv H; auto.
  repeat intro.
  inv H0.
  simpl in H; destruct H.
  subst.
  assert (wf1 (CP m i c om pi, S2.Loc (l, CP m0 i0 c0 om0 pi0) :: s3, rho2, sigma2)).
  apply H1; left; auto.
  inv H; constructor; auto with datatypes.
  apply H1; auto with datatypes.
  destruct (Hwf3 _ _ H0); auto.

  destruct (Hwf3 _ _ HL); auto.
  assert (wf1 (CP m i c om pi, S2.Loc (l, CP m0 i0 c0 om0 pi0) :: s3, rho2,sigma2)).
  apply H0.
  left; auto.
  inv H2.
  apply H24; left; auto.

  eapply equiv_upd_thread with (omg:=omg); eauto.
  destruct (Hwf3 _ _ HL); auto.  
  repeat (constructor;simpl;auto).
  repeat (constructor;simpl;auto).
  repeat (constructor;auto).
  unfold rho1', rho2'; intros z.
  unfold S2.local_of_list; destruct (eq_var z 0).
  subst.
  repeat (constructor;auto).
  rewrite H17; repeat constructor.
  auto.
  destruct z.
  intuition.
  rewrite H18.
  simpl.
  constructor.
  split.
  repeat (constructor;auto).
  auto.
  (* MonitorEnter *)
  inv H8.
  inv H1.
  inv H9.
  inv H1.
  exists None.
  exists (S2.upd_thread L2 o2 ((CP m (S2.next_line i) c om (S2.incr_lVect pi m c (i,S i)), s3, rho2) :: s2)).
  exists sigma2.
  exists omg.
  split.
  econstructor 3; eauto.
  inv H0; inv H7; simpl in *; auto.
  split.
  eapply equiv_upd_thread with (omg:=omg); eauto.
  destruct (Hwf3 _ _ HL); auto.
  repeat (constructor; auto).
  split; auto.
  repeat (constructor; auto).
  (* MonitorExit *)
  inv H8.
  inv H1.
  inv H9.
  inv H1.
  clear He5.
  exists None.
  exists (S2.upd_thread L2 o2 ((CP m (S2.next_line i) c om (S2.incr_lVect pi m c (i,S i)), s3, rho2) :: s2)).
  exists sigma2.
  exists omg.
  split.
  econstructor 4; eauto.
  inv H0; inv H7; simpl in *; auto.
  split.
  eapply equiv_upd_thread with (omg:=omg); eauto.
  destruct (Hwf3 _ _ HL); auto.
  repeat (constructor; auto).
  split; auto.
  repeat (constructor; auto).
Qed.

Lemma step3_equiv2 : forall o1 o2 sigma1 sigma2 sigma2' cs1 cs2 mu mu' L1 L2 L2' a2 omg omg',
  S1.wf_heap sigma1 ->
  wf sigma2 -> wf' L2 sigma2 omg -> L2 o2 = Some cs2 ->
  (forall f, In f cs1 ->
    match f with (_,_,_,s,_) => forall o, In (S1.Loc o) s -> sigma1 o <> None end) ->
  L1 ~t L2 -> o1 ~ml' o2 -> cs1 ~cs cs2 -> sigma1 ~h sigma2 -> 
  S2.step3 p L2 (o2,cs2,sigma2,mu,omg) (L2',sigma2',mu',omg') a2 ->
  exists a1, exists L1', exists sigma1',  
  S1.step3 p L1 (o1,cs1,sigma1,mu) (L1',sigma1',mu') a1 /\
  L1' ~t L2' /\ a1 ~a a2 /\ sigma1' ~h sigma2'.
Proof.
  intros o1 o2 sigma1 sigma2 sigma2' cs1 cs2 mu mu' L1 L2 L2' a2 omg omg' Hwf1 Hwf2 Hwf3 Hs.
  intros He5 H6 H7 H8 H10 H11.
  inv H11.
  (* step2 *)
  elim step2_equiv2 with o1 o2 sigma1 sigma2 sigma2' cs1 cs2 cs' a2 omg omg'; auto.
  intros a1 [cs1' [sigma1' [T1 [T2 [T3 T4]]]]].
  exists a1.
  exists (S1.upd_thread L1 o1 cs1').
  exists sigma1'.
  split.
  constructor 1; auto.
  split; auto.
  eapply equiv_upd_thread with (omg:=omg); eauto.
  destruct (Hwf3 _ _ Hs); auto.
  (* run *)
  inv H8.
  inv H2.
  inv H4.
  inv H2.
  inv H1.
  exists (None).
  set (rho1':=fun x =>
        if eq_var x 0 then S1.Loc (a0, make_new_context m0 i0 cid c0)
          else S1.Null).
  set (rho2':=S2.local_of_list (S2.Loc (a0, CP m0 i0 c0 om0 pi0)) nil).
  set (c1:=make_call_context m i c (make_new_context m0 i0 cid c0)).
  set (o:=(a0, make_new_context m0 i0 cid c0)).
  exists ((S1.upd_thread 
              (S1.upd_thread L1 o1 ((m,S1.next_line i,c,s2,rho1)::s1))
              (fst o, Some (snd o)) ((m1,0,c1,nil,rho1')::nil))).
  exists sigma1.
  split.
  econstructor 2; unfold o in *; eauto.
  simpl; rewrite class_make_new_context.
  congruence.
  congruence.
  unfold rho1'; simpl.
  destruct (eq_var 0 0); intuition.
  intros; simpl.
  unfold rho1'; simpl.
  destruct (eq_var (S x) 0); auto.
  congruence.
  simpl; intros.
  destruct H6.
  destruct H0 as [_ H0]; destruct (H0 a0).
  apply H4.
  intros.
  case_eq (L2 (a0,c3)); intros; auto.
  rewrite H23 in H6; discriminate.
  split.
  eapply equiv_upd_thread with (omg:=omg); eauto.
  repeat intro.
  unfold S2.upd_thread in *.
  MLcase2' o2 o0.
  destruct (Hwf3 _ _ Hs); auto.
  split; auto.
  inv H; auto.
  repeat intro.
  simpl in H; destruct H.
  subst.
  assert (wf1 (CP m i c om pi, S2.Loc (a0, CP m0 i0 c0 om0 pi0) :: s', rho, sigma2')).
  apply H0; left; auto.
  inv H; constructor; auto with datatypes.
  apply H0; auto with datatypes.
  destruct (Hwf3 _ _ H); auto.

  destruct (Hwf3 _ _ Hs); auto.
  assert (wf1 (CP m i c om pi, S2.Loc (a0, CP m0 i0 c0 om0 pi0) :: s', rho,sigma2')).
  apply H.
  left; auto.
  inv H1.
  apply H20; left; auto.

  eapply equiv_upd_thread with (omg:=omg); eauto.
  destruct (Hwf3 _ _ Hs); auto.  
  repeat (constructor;auto).
  constructor.
  simpl; constructor.
  congruence.
  repeat (constructor;auto).
  unfold c1.
  assert (cid=cId) by congruence.
  rewrite H.
  repeat (constructor;auto).
  unfold rho1', rho2'; intros z.
  unfold S2.local_of_list; destruct (eq_var z 0).
  subst.
  repeat (constructor;auto).
  destruct z.
  intuition.
  simpl.
  constructor.
  split.
  repeat (constructor;auto).
  auto.
  (* MonitorEnter *)
  inv H8.
  inv H2.
  inv H4.
  inv H2.
  exists None.
  exists (S1.upd_thread L1 o1 ((m,S1.next_line i,c, s2, rho1) :: s1)).
  exists sigma1.
  split.
  econstructor 3; eauto.
  inv H1; inv H7; simpl in *; auto.
  split.
  eapply equiv_upd_thread with (omg:=omg'); eauto.
  destruct (Hwf3 _ _ Hs); auto.
  repeat (constructor; auto).
  split; auto.
  repeat (constructor; auto).
  (* MonitorExit *)
  inv H8.
  inv H2.
  inv H4.
  inv H2.
  exists None.
  exists (S1.upd_thread L1 o1 ((m,S1.next_line i,c, s2, rho1) :: s1)).
  exists sigma1.
  split.
  econstructor 4; eauto.
  inv H1; inv H7; simpl in *; auto.
  split.
  eapply equiv_upd_thread with (omg:=omg'); eauto.
  destruct (Hwf3 _ _ Hs); auto.
  repeat (constructor; auto).
  split; auto.
  repeat (constructor; auto).
Qed.
  
Lemma step_equiv : forall sigma1 sigma2 sigma1' mu mu' L1 L2 L1' a1 omg,
  S1.wf_heap sigma1 ->
  wf sigma2 -> wf' L2 sigma2 omg ->
  (forall o cs f, L2 o = Some cs -> In f cs ->
    match f with (_,s,_) => forall o, In (S2.Loc o) s -> sigma2 o <> None end) ->
  L1 ~t L2 -> sigma1 ~h sigma2 -> 
  S1.step p (L1,sigma1,mu) (L1',sigma1',mu') a1 ->
  exists a2, exists L2', exists sigma2', exists omg',
  S2.step p (L2,sigma2,mu,omg) (L2',sigma2',mu',omg') a2 /\
  L1' ~t L2' /\ a1 ~a a2 /\ sigma1' ~h sigma2'.
Proof.
  intros sigma1 sigma2 sigma1' mu mu' L1 L2 L1' a1 omg Hwf1 Hwf2 Hwf3 He2 H8 H9 H10.
  inv H10.
  elim H8; intros.
  elim (H o); try congruence.
  intros o2 [V1 V2].
  rewrite H7 in V2; inv V2.
  inv H3.
  elim step3_equiv with o o2 sigma1 sigma2 sigma1' (fr::cs) (v2::s2) mu mu' L1 L2 L1' a1 omg; auto.
  intros a2 [L2' [sigma2' [omg' T]]].
  decompose [and] T; clear T.
  exists a2; exists L2'; exists sigma2'; exists omg'.
  split.
  repeat (econstructor; eauto).
  auto.
  intros.
  eapply He2; eauto.
  constructor; auto.
Qed.

Lemma step_equiv2 : forall sigma1 sigma2 sigma2' mu mu' L1 L2 L2' a2 omg omg',
  S1.wf_heap sigma1 ->
  wf sigma2 ->  wf' L2 sigma2 omg ->
  (forall o cs f, L1 o = Some cs -> In f cs ->
    match f with (_,_,_,s,_) => forall o, In (S1.Loc o) s -> sigma1 o <> None end) ->
  L1 ~t L2 -> sigma1 ~h sigma2 -> 
  S2.step p (L2,sigma2,mu,omg) (L2',sigma2',mu',omg') a2 ->
  exists a1, exists L1', exists sigma1', 
  S1.step p (L1,sigma1,mu) (L1',sigma1',mu') a1 /\
  L1' ~t L2' /\ a1 ~a a2 /\ sigma1' ~h sigma2'.
Proof.
  intros sigma1 sigma2 sigma2' mu mu' L1 L2 L2' a1 omg omg' Hwf1 Hwf2 Hwf3 He2 H8 H9 H10.
  inv H10.
  elim H8; intros.
  destruct H0.
  elim (H0 o); try congruence.
  intros o2 [V1 V2].
  rewrite H12 in V2; inv V2.
  inv H4.
  elim step3_equiv2 with o2 o sigma1 sigma2 sigma2' (v1::s1)  (fr::cs) mu mu' L1 L2 L2' a1 omg omg'; auto.
  intros a2 [L1' [sigma1' T]].
  decompose [and] T; clear T.
  exists a2; exists L1'; exists sigma1'.
  split.
  repeat (econstructor; eauto).
  auto.
  intros.
  eapply He2; eauto.
  constructor; auto.
Qed.

Lemma init_equiv : 
  match S1.init p, S2.init p with
    | (L1,sigma1,mu1), (L2,sigma2,mu2,omg) =>
      L1 ~t L2 /\ sigma1 ~h sigma2 /\ mu1=mu2
  end.
Proof.
  intros; unfold S1.init, S2.init.
  repeat split; auto; intros.
  unfold S1.threads_init in *.
  destruct (S1.eq_memloc' m1 (S1.run_address, None)); try discriminate.
  subst.
  exists (S2.run_address, None).
  split.
  subst; simpl.
  unfold S1.run_address, S2.run_address, S2.cp_run_address, S1.init_p.
  econstructor.
  unfold S2.threads_init.
  destruct S2.eq_memloc'; subst.
  repeat constructor.
  unfold S2.cp_init.
  repeat constructor.
  intuition.
  intuition.

  unfold S2.threads_init in *.
  destruct S2.eq_memloc'; try discriminate.
  subst.
  exists (S1.run_address, None).
  split.
  subst; simpl.
  unfold S1.run_address, S2.run_address, S2.cp_run_address, S1.init_p.
  econstructor.
  unfold S1.threads_init.
  destruct S1.eq_memloc'; intuition.
  repeat constructor.
  unfold S2.cp_init.
  repeat constructor.
  intuition.

  unfold S1.threads_init, S2.threads_init in *.
  destruct S2.eq_memloc'; intuition.
  inv e.
  generalize (H None).
  unfold location in *.
  destruct S1.eq_memloc'.
  intros; discriminate.
  elim n; auto.

  unfold S1.threads_init, S2.threads_init in *.
  destruct S1.eq_memloc'; auto.
  inv e.
  generalize (H None).
  unfold location in *.
  destruct S2.eq_memloc'.
  congruence.
  intuition.

  unfold S1.sigma_init, S2.sigma_init in *.
  destruct (S1.eq_memloc m1 (S1.run_address, S1.init_p p)); intuition.
  exists (S2.run_address, S2.cp_run_address p); intuition.
  subst.
  unfold S1.run_address, S2.run_address, S2.cp_run_address, S1.init_p.
  constructor; auto.
  apply foo_prop.
  MLcase2 (S2.run_address, S2.cp_run_address p) (S2.run_address, S2.cp_run_address p); intuition.
  repeat constructor.

  unfold S1.sigma_init, S2.sigma_init in *.
  destruct (S2.eq_memloc m2 (S2.run_address, S2.cp_run_address p)); intuition.
  subst.
  unfold S1.run_address, S2.run_address, S2.cp_run_address, S1.init_p.
  exists (1%positive,make_new_context (foo p) 0 (c_name (main_class p)) init_mcontext).
  repeat econstructor; eauto.
  apply foo_prop.
  destruct (S1.eq_memloc (@pair positive pcontext xH
            (make_new_context (foo p) O (c_name (main_class p)) init_mcontext))
         (@pair location pcontext xH
            (make_new_context (foo p) O (c_name (main_class p)) init_mcontext))).
  repeat constructor.
  intuition.

  unfold S1.fresh, S2.fresh in *.
  unfold S1.sigma_init, S2.sigma_init in *.
  intros.
  unfold S2.inDom.
  MLcase2 (a, p0) (S2.run_address, S2.cp_run_address p); auto.
  inv e.
  generalize (H (S1.init_p p)); intros.
  destruct (S1.eq_memloc (@pair location pcontext S2.run_address (S1.init_p p))
             (@pair location pcontext S1.run_address (S1.init_p p))).
  discriminate.
  elim n; auto.

  unfold S1.fresh, S2.fresh in *.
  unfold S1.sigma_init, S2.sigma_init in *.
  intros.
  unfold S2.inDom in *.
  destruct S1.eq_memloc.
  inv e.
  elim H with (S2.cp_run_address p).
  clear H.
  destruct S2.eq_memloc.
  congruence.
  intuition.
  auto.
Qed.

Lemma reach_equiv_aux : 
  forall st, 
    S1.reachable p st ->
    match st with (L1,sigma1,mu) =>
      exists L2, exists sigma2, exists omg,
        S2.reachable p (L2,sigma2,mu,omg) /\ L1 ~t L2 /\ sigma1 ~h sigma2
    end.
Proof.
  intros until st.
  induction 1.
  generalize (S2.reachable_0 p).
  case_eq (S2.init p); intros [[L2 sigma2] mu2] omg2.
  unfold S1.init.
  intros.
  replace ((fun _:location => Free):S2.lock) with mu2 in *.
  intros; exists L2; exists sigma2; exists omg2; split; auto.
  generalize init_equiv.
  rewrite H; unfold S1.init.
  intuition.
  unfold S2.init, location in *.
  congruence.
  destruct st as [[L sigma]mu].
  destruct IHreachable as [L2 [sigma2 [omg [B [B1 B2]]]]].
  destruct st' as [[L' sigma']mu'].
  elim step_equiv with (L2:=L2) (sigma2:=sigma2) (omg:=omg) (7:=H'); auto.
  intros a2 [L2' [sigma2' [omg' T]]].
  decompose [and] T.
  exists L2'; exists sigma2'; exists omg'; split; intuition.
  constructor 2 with (L2,sigma2,mu,omg) a2; auto.
  generalize (I1.reachable_wf_heap _ _ H); auto.
  generalize (wf_reach _ _ B); auto.
  generalize (reachable_wf' _ _ B); auto.
  intros.
  generalize (reachable_wf' _ _ B); unfold wf'; intros.
  destruct (H2 _ _ H0); clear H2.
  generalize (H3 _ H1); clear H3; intros H3.
  inv H3.
  eauto.
Qed.

Lemma reach_equiv_aux2 : 
  forall st, 
    S2.reachable p st ->
    match st with (L2,sigma2,mu,omg) =>
      exists L1, exists sigma1,
        S1.reachable p (L1,sigma1,mu) /\ L1 ~t L2 /\ sigma1 ~h sigma2
    end.
Proof.
  intros until st.
  induction 1.
  generalize (S1.reachable_0 p).
  case_eq (S1.init p); intros [L1 sigma1] mu1.
  unfold S2.init.
  intros.
  replace ((fun _:location => Free):S1.lock) with mu1 in *.
  intros; exists L1; exists sigma1; split; auto.
  generalize init_equiv.
  rewrite H; unfold S2.init.
  intuition.
  unfold S1.init, location in *.
  congruence.
  destruct st as [[[L sigma]mu]omg].
  destruct IHreachable as [L1 [sigma1 [B [B1 B2]]]].
  destruct st' as [[[L' sigma']mu']omg'].
  elim step_equiv2 with (L1:=L1) (sigma1:=sigma1) (7:=H'); auto.
  intros a1 [L1' [sigma1' T]].
  decompose [and] T.
  exists L1'; exists sigma1'; split; intuition.
  constructor 2 with (L1,sigma1,mu) a1; auto.
  generalize (I1.reachable_wf_heap _ _ B); auto.
  generalize (wf_reach _ _ H); auto.
  intros.
  generalize (reachable_wf' _ _ H); unfold wf'; intros.
  destruct (H0 _ _ H1); clear H0.
  auto.
  intros.
  intros.
  generalize (I1.reachable_wf _ _ B); unfold wf; intros.
  destruct (H2 _ _ H0); clear H2.
  generalize (H3 _ H1); intros.
  inv H2.
  eauto.
Qed.

Lemma reach_equiv : 
  forall st1, 
    S1.reachable p st1 ->
    exists st2, S2.reachable p st2 /\ equiv_state st1 st2.
Proof.
  destruct st1 as [[L1 sigma1]mu]; intros.
  destruct (reach_equiv_aux _ H) as [L2 [sigma2 [omg [T1 [T2 T3]]]]].
  exists (L2,sigma2,mu,omg).
  repeat (econstructor; eauto).
Qed.

Lemma reach_equiv2 : 
  forall st2, 
    S2.reachable p st2 ->
    exists st1, S1.reachable p st1 /\ equiv_state st1 st2.
Proof.
  destruct st2 as [[[L2 sigma2]mu]omg]; intros.
  destruct (reach_equiv_aux2 _ H) as [L1 [sigma1 [T1 [T2 T3]]]].
  exists (L1,sigma1,mu).
  repeat (econstructor; eauto).
Qed.

Lemma owner_in_dom : forall p L1 sigma1 mu mem o1 R o2,
  I1.wf L1 sigma1 ->
  S1.step p (L1, sigma1, mu) mem (Some (o1, R, o2)) ->
  I1.wf_h sigma1 o1.
Proof.
  intros.
  inv H0.
  destruct (H _ _ H7).
  inv H6; auto.
  inv H13.
  inv H10.
  inv HYP2; auto.
Qed.

Lemma race_equiv : 
  forall t1 t2 ppt ppt',
    S1.race p t1 t2 ppt ppt' -> 
    exists t1', exists t2', 
      S2.race p t1' t2' ppt ppt' /\ t1 ~ml' t1' /\ t2 ~ml' t2'.
Proof.
  intros.
  inv H.
  destruct st as [[L1 sigma1]mu].
  assert (exists L2, exists sigma2, exists omg,
    S2.reachable p (L2,sigma2,mu,omg) /\ L1 ~t L2 /\ sigma1 ~h sigma2).
  apply reach_equiv_aux with (1:=H0); auto.
  destruct H as [L2 [sigma2 [omg [T1 [T2 T3]]]]].
  destruct st1 as [[L1' sigma1']mu'].
  assert (WF1:=reachable_wf' _ _ T1).
  assert (WF2:=wf_reach _ _ T1).
  elim step_equiv with (L2:=L2) (sigma2:=sigma2) (omg:=omg) (7:=H1); auto.
  intros a2' [L2' [sigma2' [omg2' T]]].
  decompose [and] T; clear T.
  destruct st2 as [[L1'' sigma1'']mu''].
  elim step_equiv with (L2:=L2) (sigma2:=sigma2) (omg:=omg) (7:=H2); auto.
  intros a2'' [L2'' [sigma2'' [omg2'' T']]].
  decompose [and] T'; clear T'.
  assert (S2.get_ppt ppt a2').
  inv H3; inv H6.
  inv H8; constructor.
  assert (S2.get_ppt ppt' a2'').
  inv H10; inv H4.
  inv H12; constructor.
  assert (T1':exists t1', S2.get_owner t1' a2').
  inv H14; repeat (econstructor; eauto).
  assert (T2':exists t2', S2.get_owner t2' a2'').
  inv H16; repeat (econstructor; eauto).
  destruct T1' as [t1' T1'].
  destruct T2' as [t2' T2'].
  exists t1'; exists t2'.
  split.
  econstructor 1 with (a1:=a2') (a2:=a2''); eauto.
  simpl in WF1, WF2.
  inv H8; inv H12; try (inv H7; fail); try (constructor;fail).
  assert (sigma2 o2'<>None).
  eapply wf_action_in_dom; eauto.
  assert (sigma2 o2'0<>None).
  eapply wf_action_in_dom; eauto.
  assert (fst o2' = fst o2'0).
  inv H18; inv H19; inv H7; simpl in *; auto.
  assert (o2'=o2'0).
  destruct o2'; destruct o2'0; simpl in *; subst.
  replace c with c0; auto.
  apply WF2 with l0; auto.
  subst; inv H7; inv H19; inv H18; constructor.

  intro; subst.  
  elim H24; eapply He'; eauto.
  auto.
  
  inv H8; inv H12; inv T1'; inv T2'; inv H5; inv H6; repeat constructor; auto.

  generalize (I1.reachable_wf_heap _ _ H0); auto.
  
  intros.
  destruct f as [[[[m i] c] s] rho].  
  destruct (WF1 _ _ H10); intros.
  generalize (H13 _ H12); intros.
  inv H16; eauto.
  generalize (I1.reachable_wf_heap _ _ H0); auto.
  intros.
  intros.
  destruct f as [[[[m i] c] s] rho].  
  destruct (WF1 _ _ H); intros.
  generalize (H9 _ H8); intros.
  inv H12; eauto.
Qed.

Lemma heap_reach_in_dom : forall ls o1 o2,
  (forall sigma o m f o', In sigma ls ->
    sigma o = Some m -> m f = S2.Loc o' -> sigma o' <> None) ->
  S2.heap_reach ls o1 o2 -> exists sigma, In sigma ls /\ sigma o2 <> None.
Proof.
  induction 2.
  exists sigma; split; auto.
  exists sigma; split; auto.
  eapply H; eauto.
Qed.

Lemma heap_reach_equiv : forall o1 o2 sigma1 sigma2,
  sigma1 ~h sigma2 ->
  o1 ~ml o2 -> forall ls2,
    (forall sigma o m f o', In sigma ls2 ->
      sigma o = Some m -> m f = S2.Loc o' -> sigma o' <> None) ->
    (forall sigma sigma' l p p', In sigma ls2 -> In sigma' ls2 ->
      sigma (l,p) <> None -> sigma' (l,p') <> None -> p=p') ->
    True ->
    sigma2 o2 <> None -> In sigma2 ls2 ->
    forall ls1 o1',
  S1.heap_reach ls1 o1 o1' ->
  (forall sigma1, In sigma1 ls1 -> 
    exists sigma2, In sigma2 ls2 /\ sigma1 ~h sigma2) ->
  exists o2',
    o1' ~ml o2' /\ S2.heap_reach ls2 o2 o2'.
Proof.
  induction 8; simpl; intros.
  exists o2; split; auto.
  constructor 1 with sigma2; auto.
  elim IHheap_reach; auto.
  intros l2' [L1 L2].
  elim H9 with sigma; auto.
  intros sigma' [S1 S2].
  destruct S2.
  elim H10 with l'; try congruence.
  intros o2' [O1 O2].
  rewrite H7 in O2; inv O2.
  generalize (H14 f); rewrite H8; intros.
  inv H12.
  exists m2; split; auto.
  constructor 2 with sigma' o2' a2 f; auto.
  assert (o2'=l2').
  elim heap_reach_in_dom with (2:=L2); auto.
  intros sigma3 [W1 W2].
  inv O1; inv L1.
  replace (CP m0 i c om pi) with (CP m1 i0 c0 om0 pi0); auto.
  apply (H2 sigma3 sigma' l0); auto; try congruence.
  unfold location, S2.code_pointer in *.
  rewrite <- H13; congruence.
  subst; auto.
Qed.

Lemma reachable_h_monotone : forall p ls st,
  S2.reachable_h p ls st ->
  match st with
    (L,sigma,mu,omg) => 
    forall sigma0 o, In sigma0 ls -> sigma0 o <> None -> sigma o <> None
  end.
Proof.
  induction 1; simpl; intros.
  destruct H; subst; intuition.
  destruct H1; subst; intuition.
  destruct st as [[[L1 sigma1]mu1]omg1].
  assert (sigma1 o <> None) by (red; intros; eapply IHreachable_h; eauto).
  inv H0.
  inv H14; try (elim H4; assumption).
  inv H17; try (elim H4; assumption).
  inv H13.
  inv HYP2; try (elim H4; assumption).
  destruct HYP3 as [[m2 [M1 M2]] M3].
  MLcase2 o2 o.
  congruence.
  rewrite M3 in H3; intuition.
  destruct HYP5 as [M1 [M2 M3]].
  MLcase2 (a, CP m i c om pi) o.
  congruence.
  rewrite M3 in H3; intuition.  
Qed.

Lemma wf_reachable_h : forall p ls st,
  S2.reachable_h p ls st ->
  (forall sigma sigma' l p p', In sigma ls -> In sigma' ls ->
      sigma (l,p) <> None -> sigma' (l,p') <> None -> p=p').
Proof.
  induction 1; simpl; intros.
  intuition.
  subst.
  assert (Inv.wf (S2.sigma_init p0)).
  generalize (Inv.wf_reach p0 (S2.init p0)).
  simpl.
  intros.
  apply H; constructor.
  apply (H l); auto.
  destruct st as [[[L4 sigma4]mu4]omg4].
  assert (In sigma4 l).
  apply (reachable_h_In p0 l (L4, sigma4, mu4, omg4)); eauto.
  destruct H1; subst.
  destruct H2; subst.
  assert (Inv.wf sigma').
  apply (Inv.wf_reach p0 (L, sigma', mu, omg)).
  econstructor 2; eauto.
  eapply Inv.reachable_h_reachable; eauto.
  eauto.

  assert (sigma4=sigma0 -> p1=p').
  intros; subst; eauto.
  inv H0.
  inv H15; try (apply H2; reflexivity).
  inv H18; try (apply H2; reflexivity).
  inv H14.
  inv HYP2; try (apply H2; reflexivity).
  destruct HYP3 as [[m2 [M1 M2]] M3].
  MLcase o1 (l0,p1).
  eapply (IHreachable_h sigma4 sigma'); eauto.
  congruence.
  rewrite M3 in H3; eauto.
  destruct HYP5 as [A1 [A2 A3]]. 
  MLcase (a, CP m i c om pi) (l0, p1).
  inv e.
  generalize (reachable_h_monotone _ _ _ H _ _ H1 H4).
  intros.
  elim HYP2 with p'; auto.
  rewrite A3 in H3; eauto.

  destruct H2; subst; eauto.
  assert (sigma4=sigma' -> p1=p').
  intros; subst; eauto.
  inv H0.
  inv H15; try (apply H2; reflexivity).
  inv H18; try (apply H2; reflexivity).
  inv H14.
  inv HYP2; try (apply H2; reflexivity).
  destruct HYP3 as [[m2 [M1 M2]] M3].
  MLcase o1 (l0,p').
  eapply (IHreachable_h sigma0 sigma4); eauto.
  congruence.
  rewrite M3 in H4; eauto.
  destruct HYP5 as [A1 [A2 A3]]. 
  MLcase (a, CP m i c om pi) (l0, p').
  inv e.
  generalize (reachable_h_monotone _ _ _ H _ _ H1 H3).
  intros.
  elim HYP2 with p1; auto.
  rewrite A3 in H4; eauto.
Qed.

Lemma reachable_h_reachable1 : forall p ls st,
  S1.reachable_h p ls st -> S1.reachable p st.
Proof.
  induction 1.
  constructor 1; auto.
  econstructor 2; eauto.
Qed.

Lemma reachable_h_reachable2 : forall p ls st,
  S2.reachable_h p ls st -> S2.reachable p st.
Proof.
  induction 1.
  constructor 1; auto.
  econstructor 2; eauto.
Qed.

Lemma reachable_h_equiv : 
  forall ls2 st, 
    S2.reachable_h p ls2 st ->
    match st with (L2,sigma2,mu,omg) =>
      exists ls1, exists L1, exists sigma1,
        S1.reachable_h p ls1 (L1,sigma1,mu) /\ L1 ~t L2 /\ sigma1 ~h sigma2 /\
        forall sigma1, In sigma1 ls1 -> exists sigma2, In sigma2 ls2 /\ 
          sigma1 ~h sigma2
    end.
Proof.
  intros until st.
  induction 1.
  generalize (S1.reachable_0 p).
  case_eq (S1.init p); intros [L1 sigma1] mu1.
  unfold S2.init.
  intros.
  replace ((fun _:location => Free):S1.lock) with mu1 in *.
  exists (S1.sigma_init p::nil); exists L1; exists sigma1; split; auto.
  unfold S2.lock, S1.lock in *; rewrite <- H.
  constructor 1.
  generalize init_equiv.
  rewrite H; unfold S2.init.
  intuition.
  destruct H3; intuition.
  elim H3.
  exists (S2.sigma_init p); split.
  left; auto.
  generalize init_equiv; unfold S1.init, S2.init.
  intuition.
  unfold S1.init, location in *.
  congruence.
  destruct st as [[[L0 sigma0]mu0]omg0].
  destruct IHreachable_h as [ls1 [L1 [sigma1 [B [B1 [B2 B3]]]]]].
  elim step_equiv2 with (L1:=L1) (sigma1:=sigma1) (7:=H0); auto.
  intros a1 [L1' [sigma1' T]].
  decompose [and] T.
  exists (sigma1'::ls1).
  exists L1'; exists sigma1'; split; intuition.
  constructor 2 with (L1,sigma1,mu0) a1; auto.
  simpl in H8; destruct H8.
  subst; exists sigma; eauto with datatypes.
  elim B3 with sigma2; auto.
  intros.
  exists x; destruct H10; split; auto with datatypes.
  generalize (I1.reachable_wf_heap _ _ (reachable_h_reachable1 _ _ _ B)); auto.
  generalize (wf_reach _ _ (reachable_h_reachable2 _ _ _ H)); auto.
  intros.
  generalize (reachable_wf' _ _ (reachable_h_reachable2 _ _ _ H)); unfold wf'; intros.
  destruct (H1 _ _ H2); clear H1.
  auto.
  intros.
  intros.
  generalize (I1.reachable_wf _ _ (reachable_h_reachable1 _ _ _ B)); unfold wf; intros.
  destruct (H3 _ _ H1); clear H3.
  generalize (H4 _ H2); intros.
  inv H3.
  eauto.
Qed.

End equiv.

End CountingSemanticEquiv.

