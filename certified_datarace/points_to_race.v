Require Export points_to.
Require Export standard_semantic.
Require Export semantic_equiv.

Module MakePointsToRace (S:SEMANTIC).

  Module PT := MakePointsTo S. Import PT S C.
  Module Equiv := Standard_equiv S.


  Lemma step_get_ppt1 : forall p L o m i c s rho cs sigma mu st' a1 a2,
    step3 p L (o,(m,i,c,s,rho)::cs,sigma,mu) st' a1 ->
    conflicting_actions a1 a2 ->
    get_ppt (m,i,c) a1.
  Proof.
    intros.
    inv H; try (inv H0; fail).
    inv H8; try (inv H0; fail).
    inv H7; try (inv H0; fail).
    inv HYP2; try (inv H0; fail); constructor.
  Qed.

  Lemma step_get_ppt2 : forall p L o m i c s rho cs sigma mu st' a1 a2,
    step3 p L (o,(m,i,c,s,rho)::cs,sigma,mu) st' a2 ->
    conflicting_actions a1 a2 ->
    get_ppt (m,i,c) a2.
  Proof.
    intros.
    inv H; try (inv H0; fail).
    inv H8; try (inv H0; fail).
    inv H7; try (inv H0; fail).
    inv HYP2; try (inv H0; fail); constructor.
  Qed.

  Lemma step_body_conflict : forall p L1 o1 m1 i1 c1 s1 rho1 cs1 sigma1 mu1 st1' a1 L2 o2 m2 i2 c2 s2 rho2 cs2 sigma2 mu2 st2' a2,
    step3 p L1 (o1,(m1,i1,c1,s1,rho1)::cs1,sigma1,mu1) st1' a1 ->
    step3 p L2 (o2,(m2,i2,c2,s2,rho2)::cs2,sigma2,mu2) st2' a2 ->
    conflicting_actions a1 a2 ->
    exists ins1, exists ins2,
      body m1 i1 = Some ins1 /\ body m2 i2 = Some ins2 /\ conflicting_access ins1 ins2.
  Proof.
    intros.
    inv H; try (inv H1; fail).
    inv H0; try (inv H1; fail).
    inv H9; try (inv H1; fail).
    inv H8; try (inv H1; fail).
    inv H7; try (inv H1; fail).
    inv H9; try (inv H1; fail).
    inv HYP2; try (inv H1;fail); inv HYP3; inv H1.
    destruct H11; discriminate.
    exists (GetField f0); exists (PutField f0); repeat split; auto; constructor.
    exists (PutField f0); exists (GetField f0); repeat split; auto; constructor.
    exists (PutField f0); exists (PutField f0); repeat split; auto; constructor.
  Qed.

  Lemma get_ppt_inj : forall ppt1 ppt2 a,
    get_ppt ppt1 a -> get_ppt ppt2 a -> ppt1=ppt2.
  Proof.
    intros.
    inv H; inv H0; auto.
  Qed.

  Lemma gamma_list_exists_app : forall S s1 s2,
    gamma_list S (s1++s2) ->
    exists S1, exists S2,
      length S1 = length s1 /\
      S = S1 ++ S2 /\
      gamma_list S2 s2.
  Proof.
    induction S; intros s1 s2 H; inv H.
    destruct s1; try discriminate.
    exists nil; exists nil; simpl in *; subst.
    repeat constructor.
    destruct s1.
    simpl in H2; subst.
    exists nil; exists (a::S); repeat constructor; auto.
    simpl in H2; inv H2.
    elim IHS with (1:=H4).
    intros S1 (S2,(T1,(T2,T3))).
    exists (a::S1); exists S2.
    simpl; repeat split; auto.
    congruence.
  Qed.
    

  Section reaches.
  Variable p : program.
  Variable PT : pt.

    Inductive reaches : option pcontext -> mcontext -> method -> Prop :=
    | reaches0 : reaches None init_mcontext p.(main)
    | reaches1 : forall t t' c m P S cid m' i,
      reaches t c m ->
      m.(body) i = Some Run ->
      PT.(ptS) c m i = P::S ->
      P t' ->
      get_class p t' = Some cid ->
      lookup p run cid = Some m' ->
      reaches (Some t') (make_call_context m i c t') m'
    | reaches2 : forall t c m i ms ARGS P S m' cid o,
      reaches t c m ->
      m.(body) i = Some (InvokeVirtual ms) ->
      PT.(ptS) c m i = ARGS++P::S ->
      length ARGS = length ms.(args) ->
      P o ->
      get_class p o = Some cid ->
      lookup p ms cid = Some m' ->
      reaches t (make_call_context m i c o) m'.

    Variable Hyp1 : PointsToSpec p PT.
    Variable Hyp2 : ValidReturns p.

    Lemma reaches_sound : forall st,
      reachable p st ->
      match st with (L,sigma,mu) =>
        forall o cs,
          L o = Some cs ->
          forall m i c s rho,
            In (m,i,c,s,rho) cs ->
            reaches (snd o) c m
      end.
    Proof.
      induction 1; intros.
      (**)
      simpl; intros.
      unfold threads_init in *.
      destruct eq_memloc'; subst.
      inv H; destruct H0; try (intuition; fail).
      inv H; simpl; constructor 1.
      discriminate.
      (**)
      destruct st as [[L sigma]mu].
      destruct st' as [[L' sigma']mu'].
      generalize (reachable_correct _ _ _ Hyp1 Hyp2 H).
      intros (G1,G2).
      intros.
      inv H'.
      assert (G3:=G2 _ _ H10).
      inv G3.
      inv H9; unfold upd_thread in *; repeat (destruct eq_memloc';[subst|idtac]);
        try (assert (cs=cs') by congruence; subst); eauto.
      (* step2 *)
      inv H19.
      destruct H1; eauto with datatypes; subst.
      inv H16; eauto with datatypes.
      clear H0; simpl in H1; destruct H1; subst.
      inv H0.
      unfold gamma_stack in *.
      elim gamma_list_exists_app with (1:=H7).
      intros S1 (S2,(T1,(T2,T3))).
      inv T3.
      econstructor 3; eauto with datatypes.
      simpl; congruence.
      auto.
      destruct H0; eauto with datatypes.
      inv H0; eauto with datatypes.
      eauto with datatypes.
      simpl in H1; destruct H1; eauto with datatypes.
      inv H1; eauto with datatypes.
      (* run *)
      inv H0.
      simpl in H1; destruct H1; try (intuition; fail).
      inv H0.
      inv H7.
      econstructor 2; eauto with datatypes.
      auto.
      inv H0.
      simpl in H1; destruct H1; try (intuition; fail).
      inv H0.
      inv H7.
      eauto with datatypes.
      eauto with datatypes.
      (* monitorenter *)
      inv H0.
      simpl in H1; destruct H1.
      inv H0.
      inv H7.
      eauto with datatypes.
      eauto with datatypes.
      (* monitorexit *)
      inv H0.
      simpl in H1; destruct H1.
      inv H0.
      inv H7.
      eauto with datatypes.
      eauto with datatypes.
    Qed.

  Inductive ReachablePairs' : option pcontext -> PPT -> option pcontext -> PPT -> Prop :=
  | ReachablePairs_def : forall t1 m1 i1 c1 t2 m2 i2 c2,
    reaches t1 c1 m1 ->
    reaches t2 c2 m2 ->
    OriginalPair (m1,i1) (m2,i2) ->
    ReachablePairs' t1 (m1,i1,c1) t2 (m2,i2,c2).

  Definition race_t := race.
(*  Inductive race_t (p:program) (t1 t2:memory_location') (ppt1 ppt2:method*line*mcontext) : Prop :=
    races_def : forall st st1 st2 a1 a2,
      reachable p st ->
      step p st st1 a1 ->
      step p st st2 a2 ->
      get_ppt ppt1 a1 ->
      get_ppt ppt2 a2 ->
      get_owner t1 a1 ->
      get_owner t2 a2 ->
      conflicting_actions a1 a2 ->
      race_t p t1 t2 ppt1 ppt2.
*)
  Lemma race_t_race : forall p ppt1 ppt2,
    Sem.race p ppt1 ppt2 ->
    exists t1, exists t2, exists c1, exists c2,
      race_t p t1 t2 (ppt1,c1) (ppt2,c2).
  Proof.
    intros.
    assert (R:=race_equiv _ _ _ H).
    assert (R':=Equiv.race_equiv _ _ _ R).
    inv R'.
    assert (exists t1, S.get_owner t1 a1).
    inv H3; repeat (econstructor; eauto).
    assert (exists t2, S.get_owner t2 a2).
    inv H4; repeat (econstructor; eauto).
    destruct H6 as [t1 H6].
    destruct H7 as [t2 H7].
    exists t1; exists t2.
    exists c1; exists c2.
    econstructor 1 with (a1:=a1) (a2:=a2); eauto.
  Qed.


  Lemma ReachablePairs'_sound : forall t1 t2 ppt1 ppt2,
      race_t p t1 t2 ppt1 ppt2 ->
      ReachablePairs' (snd t1) ppt1 (snd t2) ppt2.
  Proof.
    intros.
    inv H.
    destruct st as [[L sigma]mu].
    generalize H1; intros S1.
    generalize H2; intros S2.
    inv H1; inv H2.
    inv H12; try (inv H5;fail).
    inv H18; try (inv H5;fail).
    inv H15; try (inv H5;fail).
    inv H11; try (inv H6;fail).
    inv H17; try (inv H6;fail).
    inv H12; try (inv H6;fail).
    assert (reaches (snd o) c m) by (eapply (reaches_sound _ H0); eauto with datatypes).
    assert (reaches (snd o0) c0 m0) by (eapply (reaches_sound _ H0); eauto with datatypes).
    inv H3; inv H4.
    destruct ppt1 as [[m1 i1] c1].
    destruct ppt2 as [[m2 i2] c2].
    constructor 1.
    inv H5; inv HYP2; auto.
    inv H6; inv HYP3; auto.
    inv HYP2; inv HYP3; inv H7.
    destruct H18; congruence.
    econstructor; eauto; constructor.
    econstructor; eauto; constructor.
    econstructor; eauto; constructor.
  Qed.

  Definition ReachablePairs ppt1 ppt2 := exists t1, exists t2, exists c1, exists c2,
    ReachablePairs' t1 (ppt1,c1) t2 (ppt2,c2).

  Theorem ReachablePairs_sound : forall ppt1 ppt2,
    Sem.race p ppt1 ppt2 -> ReachablePairs ppt1 ppt2.
  Proof.
    unfold ReachablePairs; intros.
    elim race_t_race with (1:=H); intros t1 [t2 [c1 [c2 T]]].
    exists (snd t1); exists (snd t2); exists c1; exists c2.
    apply ReachablePairs'_sound; auto.
  Qed.

  Inductive AliasingPair' : option pcontext -> PPT -> option pcontext -> PPT -> Prop :=
  | AliasingPair_get_put : forall f t1 m1 i1 c1 t2 m2 i2 c2 o,
    ReachablePairs' t1 (m1,i1,c1) t2 (m2,i2,c2) ->
    (body m1 i1 = Some (GetField f) -> forall P S, PT.(ptS) c1 m1 i1 = P::S -> P o) ->
    (body m1 i1 = Some (PutField f) -> forall P1 P2 S, PT.(ptS) c1 m1 i1 = P1::P2::S -> P2 o) ->
    (body m2 i2 = Some (GetField f) -> forall P S, PT.(ptS) c2 m2 i2 = P::S -> P o) ->
    (body m2 i2 = Some (PutField f) -> forall P1 P2 S, PT.(ptS) c2 m2 i2 = P1::P2::S -> P2 o) ->
    (t1<>None \/ t2 <> None) ->
    AliasingPair' t1 (m1,i1,c1) t2 (m2,i2,c2).

  Lemma None_thread_unique : forall st,
    reachable p st ->
    match st with (L,sigma,mu) =>
      forall l1 l2 cs1 cs2,
        L (l1,None) = Some cs1 ->
        L (l2,None) = Some cs2 ->
        l1 = l2
    end.
  Proof.
    induction 1.
    simpl; intros.
    unfold threads_init in *.
    repeat destruct eq_memloc'; subst; try congruence.
    destruct st as [[L sigma]mu].
    destruct st' as [[L' sigma']mu'].
    intros.
    inv H'.
    inv H9; unfold upd_thread in *;
      repeat destruct eq_memloc'; subst;
        try congruence;
          try match goal with
                [ H1 : L (l1,None) = _, 
                  H2 : L (l2,None) = _ |- _ ] =>
                apply IHreachable with (1:=H1) (2:=H2)
              end.
  Qed.

  Lemma AliasingPair'_sound : forall t1 t2 ppt1 ppt2,
      race_t p t1 t2 ppt1 ppt2 ->
      AliasingPair' (snd t1) ppt1 (snd t2) ppt2.
  Proof.
    intros.
    assert (O:ReachablePairs' (snd t1) ppt1 (snd t2) ppt2) by (eapply ReachablePairs'_sound; eauto).    
    inv H.
    assert (N:=None_thread_unique _ H0).
    generalize (reachable_correct _ _ _ Hyp1 Hyp2 H0).
    destruct st as [[L sigma]mu].
    intros [G1 G2].
    inv H1; inv H2.
    assert (G3:=G2 _ _ H13).
    assert (G4:=G2 _ _ H14).
    clear G1 G2.
    inv H12; try (inv H3; fail).
    inv H11; try (inv H4; fail).
    inv H18; try (inv H3; fail).
    inv H17; try (inv H4; fail).
    inv H12; try (inv H3; fail).
    inv H15; try (inv H4; fail).
    inv G3; inv G4.
    inv H7.
    assert (T:snd t1<>None \/ snd t2<>None).    
    case_eq (snd t1);
    case_eq (snd t2); try (intuition congruence; fail).
    intros.
    inv H5; inv H6.
    elim H.
    assert (o0=o2).
    inv HYP3; congruence.
    assert (o=o1).
    inv HYP2; congruence.
    subst.
    destruct o1; destruct o2; simpl in *; subst.
    replace l with l0; eauto.
    destruct ppt1 as [[m1 i1] c1].
    destruct ppt2 as [[m2 i2] c2].
    constructor 1 with f (snd o'); auto.
    intros.
    inv HYP2; inv H3; try congruence.
    unfold gamma_stack in *; rewrite H7 in H16; inv H16; eauto with datatypes.
    intros.
    inv HYP2; inv H3; try congruence.
    unfold gamma_stack in *; rewrite H7 in H16; inv H16; inv H26; eauto with datatypes.
    intros.
    inv HYP3; inv H4; try congruence.
    unfold gamma_stack in *; rewrite H7 in H22; inv H22; eauto with datatypes.
    intros.
    inv HYP3; inv H4; try congruence.
    unfold gamma_stack in *; rewrite H7 in H22; inv H22; inv H26; eauto with datatypes.
  Qed.

  Definition AliasingPair ppt1 ppt2 := exists t1, exists t2, exists c1, exists c2,
    AliasingPair' t1 (ppt1,c1) t2 (ppt2,c2).

  Theorem AliasingPair_sound : forall ppt1 ppt2,
    Sem.race p ppt1 ppt2 -> AliasingPair ppt1 ppt2.
  Proof.
    unfold AliasingPair; intros.
    elim race_t_race with (1:=H); intros t1 [t2 [c1 [c2 T]]].
    exists (snd t1); exists (snd t2); exists c1; exists c2.
    apply AliasingPair'_sound; auto.
  Qed.

End reaches.

End MakePointsToRace.






