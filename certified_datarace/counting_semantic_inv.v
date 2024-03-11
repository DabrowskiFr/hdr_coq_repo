Require Export counting_semantic.

Module CountingSemanticInv (S:COUNTING_SEMANTIC).

  Import S C.

  Definition wf (sigma:heap) : Prop :=
    forall a p1 p2, sigma (a,p1) <> None -> sigma (a,p2) <> None -> p1=p2.

  Lemma wf_step : forall p L sigma mu L' sigma' mu' omg omg' a,
    step p (L,sigma,mu,omg) (L',sigma',mu',omg') a -> wf sigma -> wf sigma'.
  Proof.
    intros.
    inv H.
    inv H10; try assumption.
    inv H13; try assumption.
    inv H9.
    inv HYP2; try assumption.
    destruct HYP3 as [[obj [T1 T2]] T3].
    unfold wf in *; intros.
    destruct (excluded_middle (o1=(a,p1))); subst.
    destruct (excluded_middle (p1=p2)).
    assumption.
    rewrite T3 in H1; auto.
    eapply H0; eauto; congruence.
    congruence.
    destruct (excluded_middle (o1=(a,p2))); subst.
    rewrite T3 in H; try congruence.
    eapply H0; eauto; congruence.
    rewrite T3 in H; try congruence.
    rewrite T3 in H1; try congruence.
    eapply H0; eauto; congruence.

    destruct HYP5 as [T1 [T2 T3]].
    unfold wf in *; intros.
    destruct (excluded_middle ((a0, CP m i c om pi)=(a,p1))).
    inv H2.
    destruct (excluded_middle (CP m i c om pi=p2)); auto.
    rewrite T3 in H1; try congruence.
    elim HYP2 with p2; unfold inDom; auto.
    rewrite T3 in H; try congruence.
    destruct (excluded_middle ((a0, CP m i c om pi)=(a,p2))).
    inv H3.
    elim HYP2 with p1; unfold inDom; auto.
    rewrite T3 in H1; try congruence.
    apply H0 with a; try congruence.
  Qed.

  Lemma wf_reach : forall p st,
    reachable p st ->
    match st with (L,sigma,mu,omg) => wf sigma end.
  Proof.
    induction 1.
    unfold init.
    unfold sigma_init.
    intros a p1 p2.
    destruct (eq_memloc (a, p1) (run_address, cp_run_address p)).
    destruct (eq_memloc (a, p2) (run_address, cp_run_address p)).
    congruence.
    congruence.
    destruct (eq_memloc (a, p2) (run_address, cp_run_address p)).
    congruence.
    congruence.
    destruct st' as [[[L' sigma']mu']omg'].
    destruct st as [[[L sigma]mu]omg].
    eapply wf_step; eauto.
  Qed.

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
    destruct (excluded_middle (o1=o0)); subst.
    congruence.
    rewrite T; eauto.
    destruct HYP2 as [[m [T2 T3]] T].
    destruct (excluded_middle (o1=o0)); subst.
    congruence.
    rewrite T; eauto.
    eauto with datatypes.
    destruct HYP2 as [[m' [T2 T3]] T].
    destruct (excluded_middle (o1=o')); subst.
    congruence.
    rewrite T; auto.
    destruct (excluded_middle (o1=o0)); subst.
    rewrite H in T3; inv T3.
    unfold updateField in *.
    comp f f0.
    eauto with datatypes.
    eauto with datatypes.
    rewrite T in H; eauto.    
  Qed.

  Ltac MLcase x y := destruct (eq_memloc x y); [subst|idtac].

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

  Inductive wf1 : code_pointer * op_stack * local * heap -> Prop :=
  | wf1_def : forall m i c s rho sigma om pi,
    (forall x o, rho x = Loc o -> sigma o <> None) ->
    (forall o, In (Loc o) s -> sigma o <> None) ->
    (forall o m f o', sigma o = Some m -> m f = Loc o' -> sigma o' <> None) ->
    wf1 (CP m i c om pi,s,rho,sigma).

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
    MLcase (a0, CP m i c om pi) o0.
    congruence.
    rewrite T3; eauto.
    destruct HYP5 as [T1 [T2 T3]].
    MLcase (a0, CP m i c om pi) o0.
    congruence.
    rewrite T3; auto.
    simpl in H; destruct H.
    congruence.
    auto.
    destruct HYP5 as [T1 [T2 T3]].
    MLcase (a0, CP m i c om pi) o'.
    congruence.
    rewrite T3; eauto.
    MLcase (a0, CP m i c om pi) o0.
    rewrite H in T2; inv T2.
    discriminate.
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
    MLcase (a0, CP m i c om pi) o'.
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
    inv H.
    constructor; eauto.
    
    intros.
    inv H0.
    inv HYP2; try (eapply H4; eauto; fail).
    (* putfield *)
    destruct HYP3 as [[oo [T1 T2]] T3].
    MLcase o2 o0; try congruence.
    rewrite T3; auto.
    eauto.
    inv H0; eauto.
    
    inv Hw.
    intros.
    inv HYP2; eauto.
    destruct HYP3 as [[oo [T1 T2]] T3].
    MLcase o2 o0; try congruence.
    rewrite H in T2; inv T2.
    unfold updateField in H1.
    comp f0 f.
    eauto with datatypes.
    eauto.
    rewrite T3 in H; auto.
    eauto.
    (* new *)
    destruct HYP5 as [T1 [T2 T3]].
    intros.
    inv H0; constructor; eauto.
    intros.
    MLcase (a0, CP m0 i0 c0 om pi) o'.
    congruence.
    rewrite T3; auto.
    MLcase (a0, CP m0 i0 c0 om pi) o0.
    rewrite H in T2; inv T2; discriminate.
    rewrite T3 in H; eauto.
  Qed.

  Definition wf2 : call_stack * heap * mVect -> Prop :=
    fun csh => match csh with (cs,h,_) =>
      forall f, In f cs -> wf1 (f,h) end.

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
    assert (wf1 (CP m i c om pi, v_list ++ Loc (a0, CP m0 i0 c0 om0 pi0) :: s', rho, sigma)) by (apply H0; left; auto).
    clear H0.
    inv H; constructor; auto.
    intros.
    destruct x; unfold local_of_list in *.
    inv H.
    eauto with datatypes.
    destruct (le_gt_dec (S x) (length v_list)).
    apply H11.
    apply in_or_app.
    left; eapply nth_some; eauto.
    discriminate.
    destruct H; auto.
    subst.
    assert (wf1 (CP m i c om pi, v_list ++ Loc (a0, CP m0 i0 c0 om0 pi0) :: s', rho,sigma)) by (apply H0; auto); clear H0.
    inv H; constructor; auto.
    intros.
    apply H11.
    auto with datatypes.
    (* return *)
    auto.
    (* Areturn *)
    destruct H; auto.
    subst.
    assert (wf1  (p0, s', rho',sigma)) by auto.
    assert (wf1 (CP m i c om pi, v :: s, rho,sigma)) by auto; clear H0.
    inv H; inv H2; constructor; auto.
    simpl; intros.
    destruct H; auto.
    apply H13; left; auto.
  Qed.

  Lemma step2_heap_monotone : forall p o cs sigma cs' sigma' a omg omg',
    step2 p o (cs,sigma,omg) (cs',sigma',omg') a -> 
    forall o', sigma o' <> None -> sigma' o' <> None.
  Proof.
    intros.
    inv H; auto.
    eapply step1_heap_monotone; eauto.
  Qed.

  Lemma wf2_heap_monotone : forall p o mem sigma mem' sigma' a omg omg',
    step2 p o (mem,sigma,omg) (mem',sigma',omg') a -> 
    wf2 (mem,sigma,omg) ->
    forall cs, wf2 (cs,sigma,omg) -> wf2 (cs,sigma',omg').
  Proof.
    induction cs; unfold wf2 in *; simpl; intros.
    intuition.
    destruct H2; auto.
    subst.
    assert (wf1 (f,sigma)) by auto; clear H1 IHcs.
    inv H; auto.
    eapply step1_heap_monotone_wf1 with (1:=H10); eauto.
    apply H0; simpl; auto.
  Qed.

  Definition wf_h (sigma:heap) (o:memory_location') : Prop :=
    match o with
      | (l,None) => exists p, sigma (l,p) <> None
      | (l,Some p) => sigma (l,p) <> None
    end.

  Definition wf' (L:threads) (sigma:heap) (omg:mVect) : Prop :=
    forall o cs, L o = Some cs -> wf2 (cs,sigma,omg) /\ wf_h sigma o.

  Inductive wf3 : memory_location' * call_stack * heap * lock * mVect -> Prop :=
  | wf3_def : forall o cs sigma mu omg,
    wf_h sigma o -> wf2 (cs,sigma,omg) -> wf3 (o,cs,sigma,mu,omg).

  Lemma step3_wf : forall p L o cs sigma mu L' sigma' mu' a omg omg',
    step3 p L (o,cs,sigma,mu,omg) (L',sigma',mu',omg') a ->
    wf' L sigma omg -> wf3 (o,cs,sigma,mu,omg) -> wf' L' sigma' omg'.
  Proof.
    intros.
    inv H1; inv H; unfold upd_thread in *.
    (* step2 *)
    intros o0 cs0 V0.
    destruct eq_memloc'; subst.
    split; auto.
    inv V0; eapply step2_wf; eauto.
    destruct o0; destruct o; simpl in *.
    eapply step2_heap_monotone; eauto.
    destruct H4 as [p' H4].
    exists p'; eapply step2_heap_monotone; eauto.
    split; auto.
    destruct (H0 _ _ V0).
    eapply wf2_heap_monotone; eauto.
    destruct (H0 _ _ V0); auto.
    destruct o0; destruct o0; simpl in *.
    eapply step2_heap_monotone; eauto.
    destruct H1 as [p' H1].
    exists p'; eapply step2_heap_monotone; eauto.
    (* run *)
    intros o0 cs T0.
    destruct eq_memloc'; subst.
    inv T0.
    split.
    intros fr; simpl; intros.
    destruct H; try (elim H; false); subst.
    assert (wf1 (CP m i c om pi, Loc (a0, CP m0 i0 c0 om0 pi0):: s', rho, sigma')) by auto with datatypes.
    inv H; constructor; auto.
    intros.
    destruct x; unfold local_of_list in *.
    inv H.
    eauto with datatypes.    
    destruct (le_gt_dec (S x) (length (@nil val))); try congruence.
    simpl in l; apply False_ind; omega.
    simpl.
    assert (wf1 (CP m i c om pi, Loc (a0, CP m0 i0 c0 om0 pi0):: s', rho, sigma')) by auto with datatypes.
    inv H; auto with datatypes.
    split.
    destruct eq_memloc'; subst.
    inv T0.
    unfold wf2 in *.
    intros fr; simpl; intros.
    destruct H; auto with datatypes.
    assert (wf1 (CP m i c om pi,Loc (a0, CP m0 i0 c0 om0 pi0)::s',rho,sigma')) by (apply H8; left; auto).
    subst; inv H1; constructor; eauto with datatypes.
    destruct (H0 _ _ T0); eauto.
    destruct eq_memloc'; subst.
    auto.
    destruct (H0 _ _ T0); auto.
    (* MonitorEnter *)
    intros o1 cs1 T1.
    destruct eq_memloc'; subst; eauto.
    split; auto.
    inv T1; unfold wf2 in *; simpl in *; intros.
    destruct H; auto.
    subst.
    assert (wf1 (CP m i c om pi, Loc o' :: s, rho, sigma')) by (apply H8; auto).
    inv H; constructor; eauto with datatypes.
    (* MonitorExit *)
    intros o1 cs1 T1.
    destruct eq_memloc'; subst; eauto.
    split; auto.
    inv T1; unfold wf2 in *; simpl in *; intros.
    destruct H; auto.
    subst.
    assert (wf1 (CP m i c om pi, Loc o' :: s, rho, sigma')) by (apply H8; auto).
    inv H; constructor; eauto with datatypes.
  Qed.

  Lemma step_wf' : forall p L sigma mu L' sigma' mu' a omg omg',
    step p (L,sigma,mu,omg) (L',sigma',mu',omg') a ->
    wf' L sigma omg -> wf' L' sigma' omg'.
  Proof.
    intros.
    inv H.
    eapply step3_wf; eauto.
    destruct (H0 _ _ H11).
    constructor; auto.
  Qed.

  Lemma init_wf : forall p,
    match init p with
      (L,sigma,mu,omg) => wf' L sigma omg
    end.
  Proof.
    unfold init; intros.
    unfold threads_init, sigma_init.
    repeat intro.
    destruct eq_memloc'; subst.
    inv H.
    constructor.
    repeat intro.
    simpl in H; destruct H; intuition.
    unfold cp_init in *.
    subst; econstructor; intros.
    discriminate.
    elim H.
    MLcase o' (run_address,cp_run_address p); try discriminate.
    destruct eq_memloc; inv H.
    discriminate.
    simpl.
    exists (cp_run_address p).
    destruct eq_memloc; intuition; congruence.
    discriminate.
  Qed.

  Lemma reachable_wf' : forall p st,
    reachable p st ->
    match st with (L,sigma,mu,omg) => wf' L sigma omg end.
  Proof.
    induction 1.
    apply init_wf.
    destruct st as [[[L sigma]mu]omg].
    destruct st' as [[[L' sigma']mu']omg'].
    apply step_wf' with (1:=H'); auto.
  Qed.

  Lemma wf_action_in_dom : forall p L sigma mu omg st' a1 e a2,
    wf' L sigma omg ->
    step p (L,sigma,mu,omg) st' (Some (a1,e,a2)) -> sigma a2 <> None.
  Proof.
    intros.
    inv H0.
    generalize (H _ _ H8); clear H; intros [H _].
    assert (wf1 (fr, sigma)) by auto with datatypes.
    clear H.
    inv H0; inv H7.
    inv H15.
    inv H12.
    inv HYP2; eauto with datatypes.
  Qed.

  Definition mu_dom (sigma:heap) (mu:lock) : Prop :=
    forall o l n, mu o = Held l n -> exists p, sigma (l,p) <> None.

  Lemma step_mu_dom : forall p L sigma mu L' sigma' mu' a omg omg',
    wf' L sigma omg ->
    step p (L,sigma,mu,omg) (L',sigma',mu',omg') a ->
    mu_dom sigma mu -> mu_dom sigma' mu'.
  Proof.
    intros p L sigma mu L' sigma' mu' a omg omg' Hwf H H0.
    inv H.
    inv H10.
    inv H13; auto.
    inv H9; auto.
    inv HYP2; auto.
    destruct HYP3 as [[obj [T1 T2]] T3].
    unfold mu_dom in *; intros.
    elim H0 with (1:=H); intros p2 Hp.
    destruct (excluded_middle (o1=(l, p2))); subst.
    exists p2; congruence.
    exists p2; rewrite T3; eauto.

    destruct HYP5 as [T1 [T2 T3]].
    unfold mu_dom in *; intros.
    elim H0 with (1:=H); intros p2 Hp.
    destruct (excluded_middle ((a0, CP m i c om pi)=(l,p2))); subst.
    inv H1.
    exists (CP m i c om pi).
    unfold location, code_pointer in *.
    rewrite T2; congruence.
    exists p2; rewrite T3; eauto.
    
    auto.

    unfold mu_dom in *; intros.
    destruct H15.    
    destruct (excluded_middle (o0=fst o')); subst.
    destruct H2 as [[H2 H22]|[m' [H2 H22]]]; try congruence.
    assert (fst o =l) by congruence.
    subst.
    generalize (Hwf _ _ H11); clear Hwf; intros Hwf.
    destruct Hwf as [_ Hwf].
    destruct o; destruct o; simpl in *; eauto.
    assert (fst o =l) by congruence.
    subst.
    generalize (Hwf _ _ H11); clear Hwf; intros [_ Hwf].
    destruct o; destruct o; simpl in *; eauto.
    rewrite H1 in H; auto.
    elim H0 with (1:=H); intros p2 Hp; eauto.

    unfold mu_dom in *; intros.
    destruct H15.    
    destruct (excluded_middle (o0=fst o')); subst.
    destruct H2 as [[H2 H22]|[m' [H2 H22]]]; try congruence.
    assert (fst o =l) by congruence.
    subst.
    generalize (Hwf _ _ H11); clear Hwf; intros [_ Hwf].
    destruct o; destruct o; simpl in *; eauto.
    rewrite H1 in H; auto.
    elim H0 with (1:=H); intros p2 Hp; eauto.
  Qed.
    
  Lemma reachable_mu_dom' : forall p st,
    reachable p st ->
    match st with (L,sigma,mu,omg) => mu_dom sigma mu end.
  Proof.
    induction 1.
    unfold init.
    repeat intro.
    discriminate.
    destruct st as [[[L sigma]mu]omg].
    destruct st' as [[[L' sigma']mu']omg'].
    eapply step_mu_dom; eauto.
    apply reachable_wf' with (1:=H); auto.
  Qed.

  Definition wf_dom_L (L:threads) : Prop :=
    (forall l p1 p2, L (l,p1) <> None -> L (l,p2) <> None -> p1=p2)
  /\ (forall l p1 p2, L (l,p1) <> None -> p1<>p2 -> L (l,p2) = None).

Ltac Case' :=
  match goal with
    | [ _ : context f [eq_memloc' ?x ?y] |- _ ] => 
      destruct (eq_memloc' x y); [subst|idtac]
    | [ |- context f [eq_memloc' ?x ?y] ] => 
      destruct (eq_memloc' x y); [subst|idtac]
end.

  Lemma step_wf_dom_L : forall p L sigma mu L' sigma' mu' a omg omg',
    wf' L sigma omg ->
    wf sigma ->
    step p (L,sigma,mu,omg) (L',sigma',mu',omg') a ->
    wf_dom_L L -> wf_dom_L L'.
  Proof.
    unfold wf_dom_L.
    intros.
    inv H1.
    destruct H2 as [T1 T2].
    inv H12; unfold upd_thread in *.
    (* *)
    split; intros.
    Case'; Case'; try congruence;
    eapply T1; eauto; congruence.
    Case'; Case'; try congruence; eauto.
    eapply T2; eauto; congruence.
    rewrite (T2 l p1 p2) in H13; auto; congruence.
    (* *)
    simpl in *.
    split; intros.
    repeat (Case'; try congruence);
    eapply T1; eauto; congruence.
    repeat (Case'; try congruence).
    eapply T2; eauto; congruence.
    elim H2; eapply T1; eauto; congruence.
    eapply T2; eauto; congruence.
    (* *)
    simpl in *.
    split; intros.
    repeat (Case'; try congruence);
    eapply T1; eauto; congruence.
    repeat (Case'; try congruence).
    eapply T2; eauto; congruence.
    elim H2; eapply T1; eauto; congruence.
    eapply T2; eauto; congruence.
    (* *)
    simpl in *.
    split; intros.
    repeat (Case'; try congruence);
    eapply T1; eauto; congruence.
    repeat (Case'; try congruence).
    eapply T2; eauto; congruence.
    elim H2; eapply T1; eauto; congruence.
    eapply T2; eauto; congruence.
  Qed.

  Lemma reachable_wf_dom_L : forall p st,
    reachable p st ->
    match st with (L,sigma,mu,omg) => wf_dom_L L end.
  Proof.
    induction 1.
    unfold init.
    split; intros.
    unfold threads_init in *.
    destruct (eq_memloc' (l,p1) (run_address, None));
    destruct (eq_memloc' (l,p2) (run_address, None)).
    congruence.
    intuition.
    intuition.
    intuition.
    unfold threads_init in *.
    destruct (eq_memloc' (l,p1) (run_address, None));
    destruct (eq_memloc' (l,p2) (run_address, None)).
    congruence.
    intuition.
    intuition.
    intuition.
    destruct st' as [[[L' sigma']mu']omg'].
    destruct st as [[[L sigma]mu]omg].
    eapply step_wf_dom_L; eauto.
    apply reachable_wf' with (1:=H); auto.
    apply wf_reach with (1:=H); auto.
  Qed.

  Definition mu_dom2 (sigma:heap) (mu:lock) : Prop :=
    forall o l n, mu o = Held l n -> exists p, sigma (o,p) <> None.

  Lemma step_mu_dom2 : forall p L sigma mu L' sigma' mu' a omg omg',
    wf' L sigma omg ->
    step p (L,sigma,mu,omg) (L',sigma',mu',omg') a ->
    mu_dom2 sigma mu -> mu_dom2 sigma' mu'.
  Proof.
    intros p L sigma mu L' sigma' mu' a omg omg' Hwf H H0.
    inv H.
    inv H10.
    inv H13; auto.
    inv H9; auto.
    inv HYP2; auto.
    destruct HYP3 as [[obj [T1 T2]] T3].
    unfold mu_dom2 in *; intros.
    elim H0 with (1:=H); intros p2 Hp.
    destruct (excluded_middle (o1=(o0, p2))); subst.
    exists p2; congruence.
    exists p2; rewrite T3; eauto.

    destruct HYP5 as [T1 [T2 T3]].
    unfold mu_dom2 in *; intros.
    elim H0 with (1:=H); intros p2 Hp.
    destruct (excluded_middle ((a0, CP m i c om pi)=(o0,p2))); subst.
    inv H1.
    exists (CP m i c om pi).
    unfold location, code_pointer in *.
    rewrite T2; congruence.
    exists p2; rewrite T3; eauto.
    
    auto.

    unfold mu_dom2 in *; intros.
    destruct H15.    
    destruct (excluded_middle (o0=fst o')); subst.
    destruct H2 as [[H2 H22]|[m' [H2 H22]]]; try congruence.
    assert (fst o =l) by congruence.
    subst.
    generalize (Hwf _ _ H11); clear Hwf; intros Hwf.
    assert (wf1 (CP m i c om pi, Loc o' :: s, rho, sigma')).
    destruct Hwf.
    apply H3; left; auto.
    inv H3.
    exists (snd o'); destruct o'; simpl in *; eauto with datatypes.
    
    assert (fst o =l) by congruence.
    subst.
    generalize (Hwf _ _ H11); clear Hwf; intros Hwf.
    assert (wf1 (CP m i c om pi, Loc o' :: s, rho, sigma')).
    destruct Hwf.
    apply H3; left; auto.
    inv H3.
    exists (snd o'); destruct o'; simpl in *; eauto with datatypes.
    rewrite H1 in H; auto.
    elim H0 with (1:=H); intros p2 Hp; eauto.

    unfold mu_dom2 in *; intros.
    destruct H15.    
    destruct (excluded_middle (o0=fst o')); subst.
    destruct H2 as [[H2 H22]|[m' [H2 H22]]]; try congruence.
    assert (fst o =l) by congruence.
    subst.
    generalize (Hwf _ _ H11); clear Hwf; intros Hwf.
    assert (wf1 (CP m i c om pi, Loc o' :: s, rho, sigma')).
    destruct Hwf.
    apply H3; left; auto.
    inv H3.
    exists (snd o'); destruct o'; simpl in *; eauto with datatypes.
    rewrite H1 in H; auto.
    elim H0 with (1:=H); intros p2 Hp; eauto.
  Qed.
    
  Lemma reachable_mu_dom2' : forall p st,
    reachable p st ->
    match st with (L,sigma,mu,omg) => mu_dom2 sigma mu end.
  Proof.
    induction 1.
    unfold init.
    repeat intro.
    discriminate.
    destruct st as [[[L sigma]mu]omg].
    destruct st' as [[[L' sigma']mu']omg'].
    eapply step_mu_dom2; eauto.
    apply reachable_wf' with (1:=H); auto.
  Qed.

  Lemma step_owner : forall p L sigma mu st' a omg o,
    wf' L sigma omg ->
    step p (L,sigma,mu,omg) st' a ->
    get_owner o a -> wf_h sigma o.
  Proof.
    intros.
    inv H0.
    inv H8; try (inv H1;fail).
    inv H14; try (inv H1;fail).
    inv H11; try (inv H1;fail).
    inv HYP2; inv H1.
    (* getfield *)
    destruct (H _ _ H9); auto.
    (* putfield *)
    destruct (H _ _ H9); auto.
  Qed.

Lemma reachable_h_reachable : forall p ls st,
  reachable_h p ls st -> reachable p st.
Proof.
  induction 1.
  constructor 1; auto.
  econstructor 2; eauto.
Qed.

Lemma reachable_h_In : forall p ls st,
  reachable_h p ls st -> 
  match st with
    (L,sigma,mu,omg) => In sigma ls
  end.
Proof.
  induction 1.
  unfold init; auto with datatypes.
  destruct st as [[L' s]mu'].
  left; auto.
Qed.



End CountingSemanticInv.
  