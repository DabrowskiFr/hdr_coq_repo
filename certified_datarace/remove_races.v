Require Export disjointR.
Require Export counting_must_lock.

Module RemoveRace (S1:SEMANTIC) (S2:COUNTING_SEMANTIC with Module C := S1.C).

  Module DR := DisjointReachability S2.
  Module EInv := CountingSemanticEquiv S1 S2.
  Import DR TS W3 W2 W1 DP T S2 EInv Inv.


Inductive not_a_race (ls:list heap) (mu:lock) : memory_location -> location -> location -> Prop :=
  not_a_race_def : forall l l2 l2' m m2 m2' i i2 i2'
    c c2 c2' om om2 om2' pi pi2 pi2' (must_list:PPT->Prop) n n' o1 o1',

  mu l2 = Held o1 n ->
  heap_reach ls (l2,CP m2 i2 c2 om2 pi2) (l,CP m i c om pi) ->  
  must_list (m2,i2,c2) ->

  disjoint_reachability ls must_list (m,i,c) ->

  mu l2' = Held o1' n' ->
  heap_reach ls (l2',CP m2' i2' c2' om2' pi2') (l,CP m i c om pi) ->  
  must_list (m2',i2',c2')  ->

  not_a_race ls mu (l,CP m i c om pi) o1 o1'.

Inductive conflicting_actions_on (o:memory_location) (o1 o2:memory_location') : action -> action -> Prop :=
  | conflicting_actions_on_def : forall ppt1 ppt2 f k1 k2,
    o1<> o2 ->
    (k1=Put \/ k2=Put) ->
    conflicting_actions_on o o1 o2 (Some (o1,(k2,ppt1,f),o)) (Some (o2,(k1,ppt2,f),o)).

Lemma step_same_thread_determinist : forall p st st1 st2 o r1 r2 o1 o2,
  step p st st1 (Some (o,r1,o1)) ->
  step p st st2 (Some (o,r2,o2)) ->
  conflicting_actions (Some (o,r1,o1)) (Some (o,r2,o2)) ->
  Some (o,r1,o1) = Some (o,r2,o2).
Proof.
  intros.
  inv H; inv H0.
  inv H1; inv H2; inv H9; try congruence.
Qed.

Lemma conflicting_actions_equiv : forall o o1 o2 a1 a2,
  conflicting_actions_on o o1 o2 a1 a2 ->
  conflicting_actions a1 a2.
Proof.
  intros.
  inv H; constructor; auto.
Qed.
Hint Resolve conflicting_actions_equiv.

Lemma conflicting_actions_equiv' : forall a1 a2,
  conflicting_actions a1 a2 ->
  exists o, exists o1, exists o2,
    conflicting_actions_on o o1 o2 a1 a2.
Proof.
  intros.
  inv H.
  exists o'; exists o1; exists o2.
  constructor; auto.
Qed.

Lemma step_dom_L : forall p L sigma mu omg st e o o',
  step p (L, sigma, mu, omg) st (Some (o, e, o')) ->
  L o <> None.
Proof.
  intros.
  inv H.
  inv H6.
  inv H12.
  inv H9.
  inv HYP2; congruence.
Qed.

Lemma not_a_race_sound : forall p o o1 o2 ls sigma mu a a' L omg,
  wf_heap1 sigma ->
  not_a_race ls mu o (fst o1) (fst o2) ->
  conflicting_actions_on o o1 o2 a a' ->
  (forall sigma', In sigma' ls -> forall l, inDom l sigma' -> inDom l sigma) ->
  ~ Races p (L,sigma,mu,omg) a a'.
Proof.
  red; intros p o o1 o2 ls sigma mu a a' L omg Hwf Hr Hc Hd HR.
  inv HR; inv Hr.
  assert (l2=l2').
  apply (H7 (m2,i2,c2) (m2',i2',c2')
           (l,CP m i c om pi)
           (l2,CP m2 i2 c2 om2 pi2)
           (l2',CP m2' i2' c2' om2' pi2')); auto.
  subst.
  assert (CP m2' i2' c2' om2' pi2'=CP m2 i2 c2 om2 pi2).
  apply Hwf with l2'.
  destruct (heap_reach_inDom _ _ _ H9) as [sigma' [V1 V2]]; eauto.
  destruct (heap_reach_inDom _ _ _ H5) as [sigma' [V1 V2]]; eauto.
  assert (o1=o2).
  assert (WF:=reachable_wf' _ _ H).
  assert (wf_h sigma o1).  
  apply step_owner with (2:=H0); auto.
  inv Hc; constructor.
  assert (wf_h sigma o2).
  apply step_owner with (2:=H1); auto.
  inv Hc; constructor.
  assert (fst o1 = fst o2) by congruence.  
  destruct (reachable_wf_dom_L _ _ H) as [W _].
  destruct o1 as [l1 p1].
  destruct o2 as [l2 p2].
  simpl in *; subst.
  replace p1 with p2; auto.
  inv Hc.
  apply W with l2.
  eapply step_dom_L; eauto.
  eapply step_dom_L; eauto.
  intros; subst.
  elim H2.
  inv Hc; eapply step_same_thread_determinist; eauto.
Qed.

Inductive MayMust (p:program) (ppt:PPT) (may:PPT->Prop) (must:C.pcontext->Prop) : Prop :=
  | MayMust_def : 
    (forall st1 st2 a l m i c om pi,
      reachable p st1 -> 
      step p st1 st2 a -> 
      get_ppt ppt a ->
      get_target (l,CP m i c om pi) a ->
      may (m,i,c)) ->
    (forall L1 ls sigma1 mu1 omg1 st2 a o o1 pc2,
      reachable_h p ls (L1,sigma1,mu1,omg1) -> 
      step p (L1,sigma1,mu1,omg1) st2 a -> 
      get_ppt ppt a ->
      get_owner o a ->
      get_target o1 a ->
      must pc2 ->
      exists l2, exists om2, exists pi2, exists n, exists m2, exists i2, exists c2, exists cid,
        body m2 i2 = Some (New cid) /\
        pc2 = C.make_new_context m2 i2 cid c2 /\
        mu1 l2 = Held (fst o) n /\
        heap_reach ls (l2,CP m2 i2 c2 om2 pi2) o1) ->
    MayMust p ppt may must.

Definition conv (must:C.pcontext->Prop) : PPT -> Prop :=
  fun ppt =>
    match ppt with (m,i,c) =>
      forall cid, body m i = Some (New cid) -> must (C.make_new_context m i cid c)
    end.

Inductive DisjointR_prop (p:program) (Sigma:abstract_heap) (ppt1 ppt2:PPT) : Prop :=
  DisjointR_prop_def : forall may1 must1 may2 must2,
    MayMust p ppt1 may1 must1 ->
    MayMust p ppt2 may2 must2 ->
    (exists pc1, must1 pc1) ->
    (exists pc2, must2 pc2) ->
    (forall ppt, may1 ppt -> may2 ppt -> 
      abstract_disjoint_reachability p Sigma (conv (fun x => must1 x \/ must2 x)) ppt) ->
    DisjointR_prop p Sigma ppt1 ppt2.

Lemma get_action_elem : forall o o1 o2 a1 a2,
  conflicting_actions_on o o1 o2 a1 a2 ->
  get_owner o1 a1 /\ get_owner o2 a2 /\
  get_target o a1 /\ get_target o a2.
Proof.
  intros.
  inv H; repeat econstructor.
Qed.

Lemma reachable_reachable_h : forall p st,
  reachable p st -> exists ls, reachable_h p ls st.
Proof.
  induction 1.
  exists (sigma_init p::nil); constructor.
  auto.
  destruct IHreachable as [ls IH].
  destruct st' as [[[L sigma] mu] omg].
  exists (sigma::ls); econstructor; eauto.
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
    exists L, exists mu, exists omg, reachable p (L,sigma,mu,omg).
Proof.
  induction 1; simpl; intuition.
  subst.
  exists (threads_init p).
  exists (fun _:location => Free).
  exists (om_init p).
  generalize (reachable_0 p).
  unfold init; auto.
  subst.
  exists L; exists mu; exists omg.
  constructor 2 with st e; auto.
  eapply reachable_h_reachable; eauto.
Qed.

Lemma reachable_h_inDom : forall p ls st,
  reachable_h p ls st ->
  match st with (L, sigma, mu, omg) =>
    forall sigma' : heap,
      In sigma' ls ->
      forall o : memory_location, inDom o sigma' -> inDom o sigma
  end.
Proof.
  induction 1; simpl; intros.
  elim H.
  intuition.
  subst; auto.
  intuition.
  destruct H1; subst; auto.
  destruct st as [[[L' sigma''] mu'] omg'].
  eauto.
  assert (T:=IHreachable_h _ H1 _ H2).
  clear H IHreachable_h H.
  inv H0. 
  inv H11; auto. 
  inv H14; auto. 
  inv H10. 
  inv HYP2; auto. 
  destruct HYP3 as [[obj [T1 T2]] T3]. 
  destruct (excluded_middle (o2=o)); subst. 
  congruence. 
  unfold inDom; rewrite T3; auto. 
  destruct HYP5 as [T1 [T2 T3]]. 
  destruct (excluded_middle ((a, CP m i c om pi)=o)); subst. 
  congruence. 
  unfold inDom; rewrite T3; auto. 
Qed.

Lemma remove_race_correct_aux : forall p Sigma ppt1 ppt2,
  safe_loop p ->
  (forall st, reachable p st -> match st with (_,sigma,_,_) => heap_abs sigma Sigma end) ->
  DisjointR_prop p Sigma ppt1 ppt2 ->
  forall st a1 a2,
    get_ppt ppt1 a1 ->
    get_ppt ppt2 a2 ->
    ~Races p st a1 a2.
Proof.
  intros p Sigma ppt1 ppt2 SLoop H H0 st a1 a2 H1 H2.
  intros.
  destruct st as [[[L sigma] mu] omg].
  intro T; inversion T; subst.
  assert (HH:=H _ H3); rename H into Hh; simpl in HH.
  destruct (reachable_reachable_h _ _ H3) as [ls RR].
  inv H0.
  destruct H9 as [pc1 H9].
  destruct H10 as [pc2 H10].
  destruct (conflicting_actions_equiv' _ _ H7) as [o [o1 [o2 V]]].
  destruct (get_action_elem _ _ _ _ _ V) as [A1 [A2 [A3 A4]]].
  inv H.
  destruct o as [l [m i c om pi]].
  assert (V1:=H0 _ _ _ _ _ _ _ _ _ H3 H4 H1 A3); clear H0.
  assert (V2:=H12 _ _ _ _ _ _ _ _ _ pc1 RR H4 H1 A1 A3 H9); clear H12.
  destruct V2 as [l2 [om2 [pi2 [n [m2 [i2 [c2 [cid [T0 [T00 [T1 T2]]]]]]]]]]].
  inv H8.
  assert (W1:=H _ _ _ _ _ _ _ _ _ H3 H5 H2 A4); clear H.
  assert (W2:=H0 _ _ _ _ _ _ _ _ _ _ RR H5 H2 A2 A4 H10); clear H0.
  destruct W2 as [l2' [om2' [pi2' [n' [m2' [i2' [c2' [cid' [T0' [T00' [T1' T2']]]]]]]]]]].
  assert (not_a_race ls mu (l, CP m i c om pi) (fst o1) (fst o2)).
  econstructor 1 with (must_list:=(conv (fun x => must1 x \/ must2 x))); eauto.
  simpl.
  intros.
  rewrite H in T0; inv T0; auto.
  apply disjointR_safety with p L sigma mu omg Sigma; auto.
  apply unicity; auto.
  apply reachable_h_inDom with (1:=RR).
  intros.
  destruct (reachable_h_reachable_exists _ _ _ RR _ H) as [L1 [mu1 [omg1 E]]].
  apply Hh with (1:=E).
  simpl.
  intros.
  rewrite H in T0'; inv T0'; auto.
  elim not_a_race_sound with (2:=H) (5:=T).
  unfold wf_heap1; intros.
  unfold inDom in *.
  apply (wf_reach _ _ (reachable_h_reachable _ _ _ RR)) with a; auto.
  auto.
  apply reachable_h_inDom with (1:=RR).
Qed.

Definition ValidReturns (p:program) : Prop :=
  forall c m, 
    In c p.(classes) -> 
    In m c.(methods) ->
    (forall i, body m i = Some Return -> m.(signature).(rtype) = None)
    /\
    forall i, body m i = Some AReturn -> m.(signature).(rtype) <> None.

Module ML := CountingMustLock S1 S2.

Import ML CPT PTR PT.

Definition RemoveRace p PT ML Sigma ppt1 ppt2 : Prop :=
  let must1 := mustLock PT ML ppt1 in 
  let must2 := mustLock PT ML ppt2 in 
  let may1 :=  CPT.MayTarget PT ppt1 in
  let may2 :=  CPT.MayTarget PT ppt2 in
    (exists pc1, must1 pc1) /\
    (exists pc2, must2 pc2) /\
    (forall ppt, may1 ppt -> may2 ppt -> 
      abstract_disjoint_reachability p Sigma (conv (fun x => must1 x \/ must2 x)) ppt).

Lemma remove_race_correct : forall p PT ML M Frs Sigma,
  safe_loop p ->
  PointsToSpec p PT ->
  P.MustLockSpec p PT.(ptL) PT.(ptM) ML ->
  typing p PT.(ptM) M Frs Sigma ->
  ValidReturns p ->
  forall t1 t2 ppt1 ppt2,
    RemoveRace p PT ML Sigma ppt1 ppt2 ->
    ~ race p t1 t2 ppt1 ppt2.
Proof.
  intros.
  assert (forall st a1 a2,
    get_ppt ppt1 a1 ->
    get_ppt ppt2 a2 ->
    ~Races p st a1 a2).
  intros.
  eapply remove_race_correct_aux with (Sigma:=Sigma); eauto.
  clear - H2 H0 H3.
  intros st Hr.
  destruct st as [[[L sigma]mu]omg].
  elim reachable_reachable_h with (1:=Hr).
  intros ls Hr'.
  assert (TS.SafeCG p PT.(ptM)).
  unfold TS.SafeCG.
  intros.
  eapply CPT.reachable_correct; eauto.
  eapply heap_abs_result; eauto.
  unfold RemoveRace in H4.
  destruct H4 as [O1 [O2 O3]].
  constructor 1 with
    (CPT.MayTarget PT ppt1) (mustLock PT ML ppt1)
    (CPT.MayTarget PT ppt2) (mustLock PT ML ppt2); auto.
  split.
  intros; eapply CPT.MayTarget_correct; eauto.
  intros; eapply MustLock_correct; eauto.
  split.
  intros; eapply CPT.MayTarget_correct; eauto.
  intros; eapply MustLock_correct; eauto.
  intro R; inv R.
  elim H5 with st a1 a2; auto.
  constructor 1 with st1 st2; auto.
  inv H13.
  congruence.
Qed.

Inductive UnlockedPairs' (p:program) 
  (PT:pt) (ML:P.ml) (Sigma:abstract_heap) 
  (ppt1 ppt2:PPT) : Prop :=
  UnlockedPairs_def : forall t1 t2,
    AliasingPair' p PT t1 ppt1 t2 ppt2 ->
    ~ RemoveRace p PT ML Sigma ppt1 ppt2 ->
    UnlockedPairs' p PT ML Sigma ppt1 ppt2.

Theorem UnlockedPairs'_sound : forall p PT ML M Frs Sigma,
  safe_loop p ->
  PointsToSpec p PT ->
  P.MustLockSpec p PT.(ptL) PT.(ptM) ML ->
  typing p PT.(ptM) M Frs Sigma ->
  ValidReturns p ->
  forall t1 t2 ppt1 ppt2,
    S1.race p t1 t2 ppt1 ppt2 ->
    UnlockedPairs' p PT ML Sigma ppt1 ppt2.
Proof.  
  intros.
  elim race_equiv with (1:=H4); intros t1' [t2' [T1 [T2 T3]]]  .
  destruct (excluded_middle (RemoveRace p PT ML Sigma ppt1 ppt2)); auto.  
  elim remove_race_correct with (1:=H) (2:=H0) (3:=H1) (4:=H2) (7:=T1); auto.
  econstructor; eauto.
  eapply PTR.AliasingPair'_sound; eauto.
Qed.

Definition UnlockedPairs (p:program) (PT:pt) (ML:P.ml) (Sigma:abstract_heap) 
  (ppt1 ppt2:Sem.PPT) : Prop :=
  exists c1, exists c2,
    UnlockedPairs' p PT ML Sigma (ppt1,c1) (ppt2,c2).

Theorem UnlockedPairs_sound : forall p PT ML M Frs Sigma,
  safe_loop p ->
  PointsToSpec p PT ->
  P.MustLockSpec p PT.(ptL) PT.(ptM) ML ->
  typing p PT.(ptM) M Frs Sigma ->
  ValidReturns p ->
  forall ppt1 ppt2,
    Sem.race p ppt1 ppt2 ->
    UnlockedPairs p PT ML Sigma ppt1 ppt2.
Proof.  
  intros.
  elim race_t_race with (1:=H4).
  intros t1 [t2 [c1 [c2 T]]].
  exists c1; exists c2.
  eapply UnlockedPairs'_sound; eauto.
Qed.

End RemoveRace.



