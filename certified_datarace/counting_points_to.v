Require Export points_to_race.
Require Export counting_semantic_equiv.

Module CountingPointsTo (S1:SEMANTIC) (S2:COUNTING_SEMANTIC with Module C := S1.C).

  Module E2 := CountingSemanticEquiv(S1)(S2).
  Module PTR := MakePointsToRace S1.
  Import PTR PT.


  Lemma In_cs_equiv : forall cs2 cs1 m i c om pi s rho,
    In (CP m i c om pi, s, rho) cs2 ->
    E2.equiv_callstack cs1 cs2 ->
    exists s', exists rho',
    In (m,i,c,s',rho') cs1.
  Proof.
    induction cs2; simpl; intros.
    intuition.
    destruct H; subst.
    inv H0.
    inv H3.
    eauto with datatypes.
    inv H0.
    elim IHcs2 with (1:=H) (2:=H5).
    intros s' [rho' IH].
    eauto with datatypes.
  Qed.

  Lemma gamma_cs'_ptM : forall p PtV PtS PtM m0 c0 n cs0 m i c s rho,
    gamma_cs' p PtV PtS PtM m0 c0 n cs0 ->
    In (m, i, c, s, rho) cs0 ->
    PtM m c.
  Proof.
    induction 1; simpl; intuition.
    inv H9; auto.
  Qed.

  Lemma reachable_correct : forall p PT,
    PointsToSpec p PT ->
    ValidReturns p ->
    forall L sigma omg mu,
      S2.reachable p (L,sigma,omg,mu) ->
      forall l cs,
        L l =Some cs ->
        forall m i c om pi s rho,
          In (CP m i c om pi, s, rho) cs -> 
          PT.(ptM) m c.
  Proof.
    intros.
    elim E2.reach_equiv2 with (1:=H1).
    intros st1 [R1 R2].
    inv R2.
    destruct H7 as [_ [H7 _]].
    destruct (H7 l) as [m1 [T1 T2]].
    congruence.
    rewrite H2 in T2; inv T2.
    destruct (reachable_correct _ (L1,sigma1,omg) _ H); auto.
    assert (G:=H8 _ _ (sym_eq H4)).
    elim In_cs_equiv with (1:=H3) (2:=H6).
    intros s' [rho' I].
    inv G.
    elim I.
    simpl in I; destruct I.
    inv H16; auto.
    eapply gamma_cs'_ptM; eauto.
  Qed.

  Definition MayTarget (PT:pt) (ppt:S2.PPT) : (S2.PPT -> Prop) :=
    let may := MayTarget PT.(ptS) ppt in
      fun ppt' =>
        match ppt' with
          (m,i,c) =>
          exists cid, 
            body m i = Some (New cid) /\ may (S2.C.make_new_context m i cid c)
        end.

  Lemma MayTarget_correct : forall p PT,
    PointsToSpec p PT ->
    ValidReturns p ->
    forall st st' a ppt l m i c om pi,
      S2.reachable p st ->
      S2.step p st st' a ->
      S2.get_ppt ppt a ->
      S2.get_target (l,CP m i c om pi) a -> 
      MayTarget PT ppt (m,i,c).
  Proof.
    intros.
    unfold MayTarget.
    elim E2.reach_equiv2 with (1:=H1).
    intros st1 [R1 R2].
    inv R2.
    destruct st' as [[[L3 sigma3] mu3] omg3].
    elim E2.step_equiv2 with (5:=H5) (6:=H6) (7:=H2).
    intros a2 [L2' [sigma2' [T1 [T2 [T3 T4]]]]].
    inv T3.
    inv H3.
    assert (PT.MayTarget PT.(ptS) ppt (snd o1')).
    apply
      (MayTarget_reachable_correct p PT
        L1 sigma1 mu (L2', sigma2', mu3) (Some (o1, e, o1')) o1' ppt
        H H0 R1 T1
      ).
    inv H3; inv H8; constructor.
    inv H3; inv H8; constructor.
    assert (E2.equiv_memory_location o1' (l, CP m i c om pi)).
    inv H8; inv H4; auto.
    constructor; auto.
    inv H10; eauto.
    generalize (E2.I1.reachable_wf_heap _ _ R1); auto.
    generalize (E2.Inv.wf_reach _ _ H1); auto.
    intros.
    generalize (E2.Inv.reachable_wf' _ _ H1); unfold E2.Inv.wf'; intros.
    destruct (H7 _ _ H8); auto.
    generalize (E2.I1.reachable_wf _ _ R1); unfold E2.I1.wf; intros.
    intros.
    destruct f as [[[[m0 i0]c0]s0]rho0].
    intros.
    destruct (H7 _ _ H8).
    generalize (H11 _ H9); intros.
    inv H13; auto.
  Qed.

End CountingPointsTo.