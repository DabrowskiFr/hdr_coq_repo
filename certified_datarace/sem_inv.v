Require Export sem.

Module SemInv (S:SEMANTIC).

  Import S.

  Ltac MLcase x y := destruct (eq_memloc x y); [subst|idtac].
  Ltac MLcase' x y := destruct (eq_memloc' x y); [subst|idtac].

Ltac Case' :=
  match goal with
    [ _ : context f [eq_memloc' ?x ?y] |- _ ] => 
    MLcase' x y
end.

  Inductive wf0 : line * op_stack * local * heap -> Prop :=
  | wf0_def : forall i s rho sigma,
    (forall x o, rho x = Loc o -> sigma o <> None) ->
    (forall o, In (Loc o) s -> sigma o <> None) ->
    (forall o m f o', sigma o = Some m -> m f = Loc o' -> sigma o' <> None) ->
    wf0 (i,s,rho,sigma).

  Lemma step0_wf : forall o ppt ins mem mem' a,
    step0 o ppt ins mem mem' a -> wf0 mem -> wf0 mem'.
  Proof.
    intros.
    inv H; inv H0; constructor; try assumption; intros.
    simpl in H; destruct H.
    discriminate.
    eauto.
    simpl in H; destruct H.
    eauto.
    eauto.
    unfold subst in *.
    comp x x0.
    apply H5; left; auto.
    eauto.
    eauto with datatypes.
    simpl in H; destruct H.
    subst; eauto with datatypes.
    destruct HYP2 as [T1 [T2 T3]].
    eauto.
    eauto with datatypes.
    destruct HYP2 as [[m [T2 T3]] T].
    MLcase o1 o0.
    congruence.
    rewrite T; eauto.
    destruct HYP2 as [[m [T2 T3]] T].
    MLcase o1 o0.
    congruence.
    rewrite T; eauto.
    eauto with datatypes.
    destruct HYP2 as [[m' [T2 T3]] T].
    MLcase o1 o'.
    congruence.
    rewrite T; auto.
    MLcase o1 o0.
    rewrite H in T3; inv T3.
    unfold updateField in *.
    comp f f0.
    eauto with datatypes.
    eauto with datatypes.
    rewrite T in H; eauto.    
  Qed.

  Lemma step0_heap_monotone : forall o ppt ins mem sigma mem' sigma' a,
    step0 o ppt ins (mem,sigma) (mem',sigma') a -> 
    forall o', sigma o' <> None -> sigma' o' <> None.
  Proof.
    intros.
    inv H; auto.
    destruct HYP2 as [[m [T1 T2]] T3].
    MLcase o1 o'.
    congruence.
    rewrite T3; auto.
  Qed.

  Lemma step0_inv : forall o ppt a i ins rho s s' sigma i' rho' sigma',
    step0 o ppt ins (i,s,rho,sigma) (i',s',rho',sigma') a ->
    wf_heap sigma -> wf_heap sigma'.
  Proof.
    intros.
    inv H; unfold wf_heap in *; intros; eauto.
    destruct HYP2 as [[m [T2 T3]] T1].
    MLcase o1 (l,c1) .
    destruct (C.eq_pcontext c1 c2).
    auto.
    rewrite T1 in H1; try congruence.
    apply H0 with l; congruence.
    MLcase o1 (l,c2) .
    rewrite T1 in H; try congruence.
    apply H0 with l; congruence.
    rewrite T1 in H,H1; try congruence.
    eauto.
  Qed.

  Inductive wf1 : method * line * C.mcontext * op_stack * local * heap -> Prop :=
  | wf1_def : forall m i c s rho sigma,
    (forall x o, rho x = Loc o -> sigma o <> None) ->
    (forall o, In (Loc o) s -> sigma o <> None) ->
    (forall o m f o', sigma o = Some m -> m f = Loc o' -> sigma o' <> None) ->
    wf1 (m,i,c,s,rho,sigma).

  Lemma step1_wf : forall o mem mem' a,
    step1 o mem mem' a -> wf1 mem -> wf1 mem'.
  Proof.
    intros.
    inv H; inv H0.
    assert (wf0 (i', s', rho', sigma')).
    apply step0_wf with (1:=HYP2).
    constructor; auto.
    inv H; constructor; auto.
    constructor; intros.
    destruct HYP5 as [T1 [T2 T3]].
    MLcase (a0, C.make_new_context m i cid c) o0.
    congruence.
    rewrite T3; eauto.
    destruct HYP5 as [T1 [T2 T3]].
    MLcase (a0, C.make_new_context m i cid c) o0.
    congruence.
    rewrite T3; auto.
    simpl in H; destruct H.
    congruence.
    auto.
    destruct HYP5 as [T1 [T2 T3]].
    MLcase (a0, C.make_new_context m i cid c) o'.
    congruence.
    rewrite T3; eauto.
    MLcase (a0, C.make_new_context m i cid c) o0.
    assert (m0=fun _ => Null).
    rewrite T2 in H.
    inv H.
    reflexivity.
    subst; congruence.
    rewrite T3 in H; eauto.
  Qed.


  Lemma step1_heap_monotone : forall o mem sigma mem' sigma' a,
    step1 o (mem,sigma) (mem',sigma') a -> 
    forall o', sigma o' <> None -> sigma' o' <> None.
  Proof.
    intros.
    inv H.
    eapply step0_heap_monotone; eauto.
    destruct HYP5 as [T1 [T2 T3]].
    MLcase (a0, C.make_new_context m i cid c) o'.
    congruence.
    rewrite T3; auto.
  Qed.

  Lemma step1_heap_monotone_wf1 : forall o mem sigma mem' sigma' a,
    step1 o (mem,sigma) (mem',sigma') a -> 
    wf1 (mem,sigma) ->
    forall fr, wf1 (fr,sigma) -> wf1 (fr,sigma').
  Proof.
    intros o mem sigma mem' sigma' a H Hw fr H0.
    assert (S:=step1_heap_monotone _ _ _ _ _ _ H).
    destruct fr as [[[[m i] c] s] rho].
    inv H0.
    constructor; eauto.
    
    intros.
    inv H.
    inv HYP2; try (eapply H9; eauto; fail).
    (* putfield *)
    destruct HYP3 as [[oo [T1 T2]] T3].
    MLcase o2 o'; try congruence.
    rewrite T3; auto.
    MLcase o0 o2.
    rewrite T2 in H0; inv H0.
    unfold updateField in H1.
    comp f0 f.
    inv Hw; eauto with datatypes.
    eauto.
    rewrite T3 in H0; eauto.
    (* new *)
    destruct HYP5 as [T1 [T2 T3]].    
    MLcase (a0, C.make_new_context m1 i0 cid c0) o'.
    congruence.
    rewrite T3; auto.
    MLcase (a0, C.make_new_context m1 i0 cid c0) o0.
    rewrite H0 in T2; inv T2; discriminate.
    rewrite T3 in H0; eauto.
  Qed.

  Lemma step1_inv : forall o mem sigma mem' sigma' a,
    step1 o (mem,sigma) (mem',sigma') a ->
    wf_heap sigma -> wf_heap sigma'.
  Proof.
    intros.
    inv H.
    eapply step0_inv; eauto.
    unfold wf_heap in *; intros.
    destruct HYP5 as [T1 [T2 T3]].
    MLcase (a0, C.make_new_context m i cid c) (l,c1).
    MLcase (a0, C.make_new_context m i cid c) (l,c2).
    congruence.
    rewrite T3 in H1; try congruence.
    inv e.
    rewrite HYP2 in H1; intuition.
    rewrite T3 in H; try congruence.
    MLcase (a0, C.make_new_context m i cid c) (l,c2).
    inv e.
    rewrite HYP2 in H; congruence.
    rewrite T3 in H1; try congruence.
    eauto.
  Qed.

  Definition wf2 : call_stack * heap -> Prop :=
    fun csh => let (cs,h) := csh in
      forall f, In f cs -> wf1 (f,h).

  Lemma nth_some : forall l n o,
    nth n l Null = Loc o -> In (Loc o) l.
  Proof.
    induction l; destruct n; simpl; intuition; try congruence.
    eauto.
  Qed.

  Lemma step2_wf : forall p o mem mem' a,
    step2 p o mem mem' a -> wf2 mem -> wf2 mem'.
  Proof.
    intros.
    inv H; simpl in *; intros.
    destruct H; eauto.
    subst; eapply step1_wf; eauto.
    eapply step1_heap_monotone_wf1; eauto.
    (* invokevirtual *)
    destruct H; subst.
    assert (wf1 (m, i, c, v_list ++ Loc o' :: s, rho, sigma)) by (apply H0; left; auto).
    clear H0.
    inv H; constructor; auto.
    intros.
    destruct x.
    assert (o'=o0) by congruence; subst.
    eauto with datatypes.
    destruct (le_gt_dec (S x) (length args)).
    rewrite H9 in H.
    apply H14.
    apply in_or_app.
    left; eapply nth_some; eauto.
    omega.
    rewrite H10 in H.
    discriminate.
    omega.
    destruct H; auto.
    subst.
    assert (wf1 (m, i, c, v_list ++ Loc o' :: s, rho,sigma)) by (apply H0; auto); clear H0.
    inv H; constructor; auto.
    intros.
    apply H14.
    auto with datatypes.
    (* return *)
    auto.
    (* Areturn *)
    destruct H; auto.
    subst.
    assert (wf1  (m', i', c', s', rho',sigma)) by auto.
    assert (wf1 (m, i, c, v :: s, rho,sigma)) by auto; clear H0.
    inv H; inv H2; constructor; auto.
    simpl; intros.
    destruct H; auto.
    apply H11; left; auto.
  Qed.

  Lemma step2_inv : forall p o cs sigma cs' sigma' a,
    step2 p o (cs,sigma) (cs',sigma') a ->
    wf_heap sigma -> wf_heap sigma'.
  Proof.
    intros.
    inv H; try assumption.
    eapply step1_inv; eauto.
  Qed.

  Lemma step2_heap_monotone : forall p o cs sigma cs' sigma' a,
    step2 p o (cs,sigma) (cs',sigma') a -> 
    forall o', sigma o' <> None -> sigma' o' <> None.
  Proof.
    intros.
    inv H; auto.
    eapply step1_heap_monotone; eauto.
  Qed.

  Lemma wf2_heap_monotone : forall p o mem sigma mem' sigma' a,
    step2 p o (mem,sigma) (mem',sigma') a -> wf2 (mem,sigma) ->
    forall cs, wf2 (cs,sigma) -> wf2 (cs,sigma').
  Proof.
    induction cs; unfold wf2 in *; simpl; intros.
    intuition.
    destruct H2; auto.
    subst.
    assert (wf1 (f,sigma)) by auto; clear H1 IHcs.
    inv H; auto.
    eapply step1_heap_monotone_wf1 with (1:=H8); eauto.
    apply H0; simpl; auto.
  Qed.

  Definition wf_h (sigma:heap) (o:memory_location') : Prop :=
    match o with
      | (l,None) => True
      | (l,Some p) => sigma (l,p) <> None
    end.

  Definition wf (L:threads) (sigma:heap) : Prop :=
    forall o cs, L o = Some cs -> 
      wf2 (cs,sigma) /\ wf_h sigma o.

  Inductive wf3 : memory_location' * call_stack * heap * lock -> Prop :=
  | wf3_def : forall o cs sigma mu,
    wf_h sigma o -> wf2 (cs,sigma) -> wf3 (o,cs,sigma,mu).

  Lemma step3_wf : forall p L o cs sigma mu L' sigma' mu' a,
    step3 p L (o,cs,sigma,mu) (L',sigma',mu') a ->
    wf L sigma -> wf3 (o,cs,sigma,mu) -> wf L' sigma'.
  Proof.
    intros.
    inv H1; inv H; unfold upd_thread in *.
    (* step2 *)
    intros o0 cs0 V0.
    MLcase' o o0.
    split; auto.
    inv V0; eapply step2_wf; eauto.
    destruct o0.
    destruct o; simpl in *; auto.
    eapply step2_heap_monotone; eauto.
    split; auto.
    destruct (H0 _ _ V0).
    eapply wf2_heap_monotone; eauto.
    destruct o0.
    destruct o0; simpl in *; auto.
    eapply step2_heap_monotone; eauto.
    destruct (H0 _ _ V0); auto.
    (* run *)
    intros o0 cs T0.
    simpl in *.
    Case'.
    inv T0.
    split.
    intros fr; simpl; intros.
    destruct H; try (elim H; false); subst.
    assert (wf1 (m, i, c, Loc o' :: s, rho, sigma')) by auto with datatypes.
    inv H; constructor; auto.
    intros.
    destruct x.
    replace o0 with o' in * by congruence.
    eauto with datatypes.    
    rewrite H17 in H; discriminate.
    assert (wf1 (m, i, c, Loc o' :: s, rho, sigma')) by auto with datatypes.
    inv H; auto with datatypes.
    destruct o'; simpl in *; auto.
    split.
    MLcase' o o0.
    inv T0.
    unfold wf2 in *.
    intros fr; simpl; intros.
    destruct H; auto with datatypes.
    assert (wf1 (m,i,c,Loc o'::s,rho,sigma')) by (apply H7; left; auto).
    subst; inv H1; constructor; eauto with datatypes.
    destruct (H0 _ _ T0); eauto.
    MLcase' o o0.
    auto.
    destruct (H0 _ _ T0); auto.
    (* MonitorEnter *)
    intros o1 cs1 T1.
    MLcase' o o1; eauto.
    split; auto.
    inv T1; unfold wf2 in *; simpl in *; intros.
    destruct H; auto.
    subst.
    assert (wf1 (m, i, c, Loc o' :: s, rho, sigma')) by (apply H7; auto).
    inv H; constructor; eauto with datatypes.
    (* MonitorExit *)
    intros o1 cs1 T1.
    MLcase' o o1; eauto.
    split; auto.
    inv T1; unfold wf2 in *; simpl in *; intros.
    destruct H; auto.
    subst.
    assert (wf1 (m, i, c, Loc o' :: s, rho, sigma')) by (apply H7; auto).
    inv H; constructor; eauto with datatypes.
  Qed.

  Lemma step3_inv : forall p L o cs sigma mu L' sigma' mu' a,
    step3 p L (o,cs,sigma,mu) (L',sigma',mu') a ->
    wf_heap sigma -> wf_heap sigma'.
  Proof.
    intros.
    inv H; try assumption.
    eapply step2_inv; eauto.
  Qed.

  Lemma step_inv : forall p L sigma mu L' sigma' mu' a,
    step p (L,sigma,mu) (L',sigma',mu') a ->
    wf_heap sigma -> wf_heap sigma'.
  Proof.
    intros.
    inv H.
    eapply step3_inv; eauto.
  Qed.

  Lemma step_wf : forall p L sigma mu L' sigma' mu' a,
    step p (L,sigma,mu) (L',sigma',mu') a ->
    wf L sigma -> wf L' sigma'.
  Proof.
    intros.
    inv H.
    eapply step3_wf; eauto.
    destruct (H0 _ _ H9).
    constructor; auto.
  Qed.

  Lemma init_wf : forall p,
    match init p with
      (L,sigma,mu) => wf L sigma
    end.
  Proof.
    unfold init; intros.
    unfold threads_init, sigma_init.
    repeat intro.
    Case'.
    inv H.
    constructor.
    repeat intro.
    simpl in H; destruct H; intuition.
    subst; constructor; intros.
    discriminate.
    elim H.
    MLcase o (run_address,init_p p); try discriminate.    
    inv H; discriminate.
    simpl; auto.
    discriminate.
  Qed.

  Lemma init_wf_heap : forall p,
    match init p with
      (L,sigma,mu) => wf_heap sigma
    end.
  Proof.
    unfold init; intros.
    repeat intro.
    unfold sigma_init in *.
    MLcase (l,c1) (run_address,init_p p); intuition.
    MLcase (l,c2) (run_address,init_p p); intuition.
    congruence.
  Qed.

  Lemma reachable_wf : forall p st,
    reachable p st ->
    match st with (L,sigma,mu) => wf L sigma end.
  Proof.
    induction 1.
    apply init_wf.
    destruct st as [[L sigma]mu].
    destruct st' as [[L' sigma']mu'].
    apply step_wf with (1:=H'); auto.
  Qed.

  Lemma reachable_wf_heap : forall p st,
    reachable p st ->
    match st with (L,sigma,mu) => wf_heap sigma end.
  Proof.
    induction 1.
    apply init_wf_heap.
    destruct st as [[L sigma]mu].
    destruct st' as [[L' sigma']mu'].
    apply step_inv with (1:=H'); auto.
  Qed.

  Lemma heap_reach_first_in_dom : forall ls o1 o2,
    heap_reach ls o1 o2 ->
    exists sigma, In sigma ls /\ sigma o1 <> None.
  Proof.
    induction 1; eauto with datatypes.
  Qed.

Lemma reachable_h_In : forall p ls st,
  reachable_h p ls st -> 
  match st with
    (L,sigma,mu) => In sigma ls
  end.
Proof.
  induction 1.
  unfold init; auto with datatypes.
  destruct st as [[L' s]mu'].
  left; auto.
Qed.

Lemma reachable_h_reachable : forall p ls st,
  reachable_h p ls st -> reachable p st.
Proof.
  induction 1.
  constructor 1; auto.
  econstructor 2; eauto.
Qed.

Lemma reachable_h_reachable_exists : forall p ls st,
  reachable_h p ls st -> 
  forall sigma, In sigma ls -> 
    exists L, exists mu, reachable p (L,sigma,mu).
Proof.
  induction 1; simpl; intuition.
  subst.
  exists (threads_init p).
  exists (fun _:location => Free).
  generalize (reachable_0 p).
  unfold init; auto.
  subst.
  exists L; exists mu.
  constructor 2 with st e; auto.
  eapply reachable_h_reachable; eauto.
Qed.

Lemma reachable_h_monotone : forall p ls st,
  reachable_h p ls st ->
  match st with
    (L,sigma,mu) => 
    forall sigma0 o, In sigma0 ls -> sigma0 o <> None -> sigma o <> None
  end.
Proof.
  induction 1; simpl; intros.
  destruct H; subst; intuition.
  destruct H1; subst; intuition.
  destruct st as [[L1 sigma1]mu1].
  assert (sigma1 o <> None) by (red; intros; eapply IHreachable_h; eauto).
  inv H0.
  inv H12; try (elim H4; assumption).
  inv H15; try (elim H4; assumption).
  inv H11.
  inv HYP2; try (elim H4; assumption).
  destruct HYP3 as [[m2 [M1 M2]] M3].
  MLcase o2 o.
  congruence.
  rewrite M3 in H3; intuition.
  destruct HYP5 as [M1 [M2 M3]].
  MLcase (a, C.make_new_context m i cid c) o.
  congruence.
  rewrite M3 in H3; intuition.  
Qed.

  Lemma reachable_h_L_Wf : forall p l st,
    reachable_h p l st ->
    match st with (L, sigma, mu) =>
      forall o z,
        L o <> None -> fst z = fst o -> L z <> None -> o = z
    end.
  Proof.
    induction 1; intros.
    unfold init.
    unfold threads_init; intros.
    destruct (eq_memloc' o (run_address, None));
    destruct (eq_memloc' z (run_address, None)).
    congruence.
    intuition.
    intuition.
    intuition.
    destruct st as [[L' sigma']mu'].
    generalize IHreachable_h; clear IHreachable_h H l.
    intros H.
    inv H0.
    inv H11; unfold upd_thread in *.
    Case'; Case'; try congruence.
    apply H; congruence.
    apply H; congruence.
    apply H; congruence.
    Case'; Case'; try congruence.
    destruct (eq_memloc' o0 o).
    subst.
    simpl in *.
    rewrite H2 in H21.
    destruct o; simpl in *; rewrite H21 in H12; discriminate.
    simpl in *.
    rewrite H2 in H21.
    destruct o; simpl in *; rewrite H21 in H1.
    intuition.
    Case'; simpl in *.
    destruct o'; destruct z; simpl in *; subst; rewrite H21 in H12; discriminate.
    Case'.
    congruence.
    apply H; congruence.
    Case'.
    simpl in *; rewrite <- H2 in H21.
    destruct z; simpl in *; rewrite H21 in H3; intuition.
    Case'.
    apply H; congruence.
    apply H; congruence.
    Case'; Case'.
    congruence.
    apply H; congruence.
    apply H; congruence.
    apply H; congruence.
    Case'; Case'.
    congruence.
    apply H; congruence.
    apply H; congruence.
    apply H; congruence.
Qed.

Lemma reachable_h_mu_dom : forall p st,
  reachable p st ->
  match st with
    (L,sigma,mu) =>
    forall o l n, mu o = Held l n -> 
      exists p, sigma (o,p) <> None
  end.
Proof.
  induction 1.
  simpl.
  congruence.
  destruct st' as [[L2 sigma2]mu2].
  destruct st as [[L1 sigma1]mu1].
  inv H'.
  destruct (reachable_wf _ _ H _ _ H8).
  assert (wf1 (fr,sigma1)) by (apply H0; left; auto); clear H0.
  inv H7.
  inv H13; try exact IHreachable.
  assert (M:=step1_heap_monotone _ _ _ _ _ _ H10).
  intros.
  elim IHreachable with (1:=H0).
  intros p0 P.
  exists p0; eauto.
  auto.
  intros.
  destruct H15.
  destruct (excluded_middle (o0=fst o')); subst.
  exists (snd o').
  inv H2.
  apply H13; left.
  destruct o'; auto.
  rewrite H3 in H0; eauto.
  intros.
  destruct H15.
  destruct (excluded_middle (o0=fst o')); subst.
  exists (snd o').
  inv H2.
  apply H13; left.
  destruct o'; auto.
  rewrite H3 in H0; eauto.
Qed.

Lemma no_race_equiv : forall p,
  (forall t1 t2 ppt1 ppt2, ~ race p t1 t2 ppt1 ppt2) ->
  (forall m1 i1 m2 i2, ~ race_without_context p (m1,i1) (m2,i2)).
Proof.
  red; intros.
  inv H0.
  assert (O1:exists o1, get_owner o1 a1).
  inv H6; repeat (econstructor; eauto).
  assert (O2:exists o2, get_owner o2 a2).
  inv H6; repeat (econstructor; eauto).
  destruct O1 as [o1 O1].
  destruct O2 as [o2 O2].
  elim H with o1 o2 (m1, i1, c1) (m2, i2, c2).
  constructor 1 with st st1 st2 a1 a2; auto.
Qed.

End SemInv.


