Require Export must_lock.
Require Export counting_points_to.

Module CountingMustLock (S1:SEMANTIC) (S2:COUNTING_SEMANTIC with Module C := S1.C).

  Module CPT := CountingPointsTo S1 S2. Import CPT PTR PT.

  Module E1 := CountingSemanticEquiv(S1)(S2).
  Module P := MakeMustLock S1. Import P.

  Import S2 C.

  Definition mustLock (PT:pt) (ML:ml) : S2.PPT -> pcontext -> Prop :=
    fun ppt pc0 =>
      P.mustLock PT.(ptL) ML ppt pc0.

Lemma reachable_h_reachable_exists : forall p ls st,
  S1.reachable_h p ls st -> 
  forall sigma, In sigma ls -> 
    exists L, exists mu, S1.reachable p (L,sigma,mu).
Proof.
  induction 1; simpl; intuition.
  subst.
  generalize (S1.reachable_0 p); unfold S1.init; eauto.
  subst.
  exists L; exists mu.
  constructor 2 with st e; auto.
  eapply I.reachable_h_reachable; eauto.
Qed.

Lemma In_equiv_cs : forall m i c s rho cs cs',
  In (m, i, c, s, rho) cs ->
  E1.equiv_callstack cs cs' ->
  exists om, exists pi, exists s', exists rho',
    In (CP m i c om pi,s',rho') cs'.
Proof.
  induction cs; simpl; intuition.
  inv H1; inv H0.
  inv H2; eauto with datatypes.
  inv H0.
  elim IHcs with (1:=H1) (2:=H5);
    intros om [pi [s' [rho' V]]].
  exists om; exists pi; exists s'; exists rho'; right; auto.
Qed.

Lemma reachable_h_intermediate : forall p ls st,
  S2.reachable_h p ls st -> 
  forall sigma, In sigma ls -> 
    (forall o m f o', sigma o = Some m -> m f = Loc o' -> sigma o' <> None).
Proof.
  induction 1.
  intros.
  destruct H; subst.
  unfold sigma_init in *.
  destruct (eq_memloc o (run_address, cp_run_address p)); try congruence.
  inv H0; congruence.
  intuition.

  intros.
  simpl in H1; destruct H1; subst; eauto.  
  inv H0.
  assert (G:=E1.reachable_h_reachable2 _ _ _ H).
  assert (W:=E1.Inv.reachable_wf' _ _ G).
  destruct (W _ _ H10).  
  assert (E1.Inv.wf1 (fr,sigma)).
  apply H0; left; auto.
  simpl; intros.
  clear IHreachable_h H.
  inv H4.
  clear H0 H10 H6 W G.
  inv H9; try (eapply H8; eauto; fail).
  inv H16; try (eapply H8; eauto; fail).
  inv H13.
  inv HYP2; try (eapply H8; eauto; fail).
  destruct HYP3 as [[m' [T1 T2]] T3].
  destruct (eq_memloc o2 o'); subst.
  congruence.
  rewrite T3; auto.
  destruct (eq_memloc o2 o); subst.
  rewrite H2 in T2; inv T2.
  unfold updateField in *.
  destruct (eq_pos f0 f); subst.
  eauto with datatypes.
  eauto.
  rewrite T3 in H2; eauto.
  destruct HYP5 as [T1 [T2 T3]].
  destruct (eq_memloc (a, CP m0 i c om pi) o).
  subst.
  rewrite T2 in H2; inv H2.
  congruence.
  rewrite T3 in H2; auto.
  destruct (eq_memloc (a, CP m0 i c om pi) o').
  subst.
  congruence.
  rewrite T3; eauto.
Qed.

Lemma heap_reach_in_dom1 : forall ls o1 o2,
  S1.heap_reach ls o1 o2 -> exists sigma, In sigma ls /\ sigma o1 <> None.
Proof.
  induction 1.
  exists sigma; split; auto.
  auto.
Qed.

Lemma reachable_h_monotone : forall p ls st,
  S1.reachable_h p ls st ->
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
  destruct (excluded_middle (o2=o)); subst.
  congruence.
  rewrite M3 in H3; intuition.
  destruct HYP5 as [M1 [M2 M3]].
  destruct (excluded_middle ((a, S1.C.make_new_context m i cid c)=o)).
  congruence.
  rewrite M3 in H3; intuition.  
Qed.


  Lemma MustLock_correct : forall p PT ML,
    PointsToSpec p PT ->
    MustLockSpec p PT.(ptL) PT.(ptM) ML ->
    ValidReturns p ->
    forall ls L sigma omg mu st2 a pc2 ppt o o1,
      reachable_h p ls (L,sigma,mu,omg) ->
      step p (L,sigma,mu,omg) st2 a ->
      get_ppt ppt a ->
      get_owner o a ->
      get_target o1 a ->
      mustLock PT ML ppt pc2 ->
      exists l2, exists om2, exists pi2, exists n, exists m2, exists i2, exists c2, exists cid,
        body m2 i2 = Some (New cid) /\
        pc2 = make_new_context m2 i2 cid c2 /\
        mu l2 = Held (fst o) n /\
        heap_reach ls (l2,CP m2 i2 c2 om2 pi2) o1.
  Proof.
    intros.
    elim (E1.reachable_h_equiv _ _ _ H2).
    intros ls1 [L1 [sigma1 [B1 [B2 [B3 B4]]]]].
    assert (P.SafeCG p PT.(ptM)).
    unfold SafeCG.
    intros.
    elim E1.reach_equiv with (1:=H8).
    intros st3 [E1 E2].
    inv E2.
    assert (T:=CPT.reachable_correct _ _ H H1 _ _ _ _ E1).
    destruct H15 as [X _].
    destruct (X l); try congruence.
    destruct H11 as [Y Z].
    rewrite H9 in Z; inv Z.
    elim In_equiv_cs with (1:=H10) (2:=H13).
    intros om [pi [s' [rho' V]]].
    eapply T; eauto.
    assert (PL:SafePtL p PT.(ptL)).
    repeat intro.
    assert (T:=CPT.PTR.PT.reachable_correct _ _ _ H H1 H9).
    destruct T as [_ T].
    assert (T1:=T _ _ H10).
    inv T1.
    apply (H22 _ _ H11).
    destruct st2 as [[[L2 sigma2] mu2] omg2].
    elim E1.step_equiv2 with (5:=B2) (6:=B3) (7:=H3).
    intros a2 [L2' [sigma2' [T1 [T2 [T3 T4]]]]].
    destruct a2; try (inv H5; inv T3; fail).
    destruct p0 as [[oo1 R] oo1'].
    elim (P.mustLock_correct _ _ PT.(ptL) _ PL H8 H0 H1
    _ _ _ _ _ (Some (oo1, R, oo1')) ppt oo1 oo1' pc2 B1 T1); auto.
    intros l2 [n [TV1 TV2]].
    elim heap_reach_in_dom1 with (1:=TV2).
    intros sigma1' [S1 S2].
    assert (S3:=reachable_h_monotone _ _ _ B1 _ _ S1 S2).   
    destruct B3 as [B7 [B5 B6]].
    elim B7 with (1:=S3).
    intros o2 [O1 O2].
    assert (sigma o2<>None).
    inv O2; [intuition|congruence]; clear O2.
    inv O1.
    exists l2; exists om; exists pi; exists n; exists m; exists i; exists c; exists cid; split; auto.
    inv T3.
    split; [auto|idtac].
    split.
    inv H5; inv H15; auto.
    elim E1.heap_reach_equiv with (l2, make_new_context m i cid c) (l2, CP m i c om pi)
      sigma1 sigma ls ls1 oo1'; auto.
    intros oo2' [R1 R2].
    assert (sigma o1 <> None).
      inv H6.
      inv H3.
      inv H21.
      inv T1.
      inv H24.
      inv H23.
      inv HYP2.
      inv HYP3; intuition; congruence.
      inv HYP3; intuition.
      destruct H3; intuition; congruence.
    assert (o1=oo2').
    eapply E1.wf_aux; eauto.
    generalize (E2.Inv.wf_reach _ _ (E2.reachable_h_reachable2 _ _ _ H2)); auto.
    elim E2.heap_reach_in_dom with (2:=R2).
    intros sigma3 [X1 X2].
    eapply (E2.reachable_h_monotone _ _ _ H2); eauto.
    intros; eapply reachable_h_intermediate; eauto.    
    inv H6; auto.
    subst; auto.
    split; auto.
    constructor; auto.
    intros; eapply (reachable_h_intermediate _ _ _ H2); eauto.
    intros; eapply (E2.wf_reachable_h _ _ _ H2 sigma0 sigma'); eauto.
    apply (E2.Inv.reachable_h_In _ _ _ H2).
    destruct (CPT.PTR.PT.reachable_correct _ _ _ H H1 (E2.reachable_h_reachable1 _ _ _ B1)).
    intros.
    generalize (H10 _ _ H11); intros.
    inv H13.
    apply H24; auto.
    inv T3.
    inv H14; inv H4; econstructor; eauto.
    inv T3.
    inv H14; inv H4; constructor.
    inv T3.
    inv H14; inv H4; constructor.
    apply (E2.I1.reachable_wf_heap _ _ (E2.reachable_h_reachable1 _ _ _ B1)).
    apply (E2.Inv.wf_reach _ _ (E2.reachable_h_reachable2 _ _ _ H2)); auto.
    apply (E1.Inv.reachable_wf' _ _ (E2.reachable_h_reachable2 _ _ _ H2)); auto.
    generalize (E1.I1.reachable_wf _ _ (E2.reachable_h_reachable1 _ _ _ B1)); intros.
    destruct (H9 _ _ H10).
    destruct f as [[[[m i] c] s0] rho].
    assert (E1.I1.wf1 (m, i, c, s0, rho,sigma1)).
    apply H12; auto.
    inv H14; auto.
  Qed.

End CountingMustLock.