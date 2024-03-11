Require Export sem.

Definition incl (A:Set) (P1 P2:A->Prop) :=
  forall a, P1 a -> P2 a.
Notation "X <= Y" := (incl _ X Y).

Inductive incl_list (A:Set) : list (A->Prop) -> list (A->Prop) -> Prop :=
| incl_list_nil : incl_list A nil nil
| incl_list_cons : forall p1 p2 q1 q2,
  p1 <= p2 -> incl_list A q1 q2 -> incl_list A (p1::q1) (p2::q2).
Notation "X <=s Y" := (incl_list _ X Y) (at level 10).

Definition incl_func (A:Set) (R1 R2:var -> A->Prop) : Prop :=
  forall x, (R1 x) <= (R2 x).
Notation "X <=l Y" := (incl_func _ X Y) (at level 10).

Definition singleton (A:Set) (x:A) : A -> Prop :=
  fun y => x=y.
Implicit Arguments singleton [A].

Module MakePointsTo (S:SEMANTIC).

  Import S C.

  Ltac MLcase x y := destruct (eq_memloc x y); [subst|idtac].
  Ltac MLcase' x y := destruct (eq_memloc' x y); [subst|idtac].


Section PointsTo.

  Variable p : program.
  Variable PtL: mcontext -> method -> line -> var -> pcontext -> Prop.
  Variable PtS: mcontext -> method -> line -> list (pcontext -> Prop).
  Variable PtF: pcontext -> field -> pcontext -> Prop.
  Variable PtR : mcontext -> method -> pcontext -> Prop.
  Variable PtM : method -> mcontext -> Prop.
  Variable PtCall : pcontext -> method_signature -> method -> Prop.

  Inductive PointsTo_instr (m:method) (i:line) (c:mcontext) : instruction -> Prop :=
  | PT_AconstNull : 
    ((fun _=>False)::(PtS c m i)) <=s (PtS c m (next_line i)) ->
    (PtL c m i) <=l (PtL c m (next_line i)) ->
    PointsTo_instr m i c AConstNull
  | PT_New : forall cl,
    (PtL c m i) <=l (PtL c m (next_line i)) ->
    ((singleton (make_new_context m i cl c))::(PtS c m i)) <=s (PtS c m (next_line i)) ->
    PointsTo_instr m i c (New cl)
  | PT_ALoad : forall x,
    (PtL c m i) <=l (PtL c m (next_line i)) ->
    ((PtL c m i x)::(PtS c m i)) <=s (PtS c m (next_line i)) ->
    PointsTo_instr m i c (ALoad x)
  | PT_AStore : forall x P S,
    PtS c m i = P::S ->
    (forall z, z<>x -> PtL c m i z <= PtL c m (next_line i) z) ->
    P <= (PtL c m (next_line i) x) ->
    S <=s (PtS c m (next_line i)) ->
    PointsTo_instr m i c (AStore x)
  | PT_GetField : forall f P1 P2 S,
    PtS c m i = P1::S ->
    (PtL c m i) <=l (PtL c m (next_line i)) ->
    (forall h, P1 h -> (PtF h f) <= P2) ->
    (P2::S) <=s (PtS c m (next_line i)) ->
    PointsTo_instr m i c (GetField f)
  | PT_PutField : forall f P1 P2 S,
    PtS c m i = P1::P2::S ->
    (PtL c m i) <=l (PtL c m (next_line i)) ->
    (forall h, P2 h -> P1 <= (PtF h f)) ->
    S <=s (PtS c m (next_line i)) ->
    PointsTo_instr m i c (PutField f)
  | PT_Ifnd : forall j,
    (PtL c m i) <=l (PtL c m (next_line i)) ->
    (PtS c m i) <=s (PtS c m (next_line i)) ->
    (PtL c m i) <=l (PtL c m j) ->
    (PtS c m i) <=s (PtS c m j) ->
    PointsTo_instr m i c (Ifnd j)
  | PT_Goto : forall j,
    (PtL c m i) <=l (PtL c m j) ->
    (PtS c m i) <=s (PtS c m j) ->
    PointsTo_instr m i c (Goto j)
  | PT_InvokeVirtual : forall ms ARGS P S,
    PtS c m i = ARGS++P::S ->
    length ARGS = length ms.(args) ->
    (PtL c m i) <=l (PtL c m (next_line i)) ->
    (forall h m', P h -> PtCall h ms m' -> PtM m' (make_call_context m i c h)) ->
    (ms.(rtype) = None -> S <=s (PtS c m (next_line i))) ->
    (ms.(rtype) <> None -> 
      ((fun h' => exists h, exists m', 
        P h /\ 
        PtCall h ms m' /\ 
        PtR (make_call_context m i c h) m' h')::S) <=s (PtS c m (next_line i))) ->
    (forall h m', P h -> PtCall h ms m' -> nil <=s (PtS (make_call_context m i c h) m' 0)) ->
    (forall h m', P h -> PtCall h ms m' -> PtL (make_call_context m i c h) m' 0 0 h) ->
    (forall h m' j Pj, 
      P h -> PtCall h ms m' -> 
      List.nth_error ARGS ((length ms.(args))-(Datatypes.S j)) = Some Pj ->
      Pj <= (PtL (make_call_context m i c h) m' 0 (Datatypes.S j))) ->
    PointsTo_instr m i c (InvokeVirtual ms)
  | PT_AReturn : forall P S,
    PtS c m i = P::S ->
    P <= PtR c m ->
    PointsTo_instr m i c AReturn
  | PT_MonitorEnter : forall P S,
    PtS c m i = P::S ->
    (PtL c m i) <=l (PtL c m (next_line i)) ->
    S <=s (PtS c m (next_line i)) ->
    PointsTo_instr m i c MonitorEnter
  | PT_MonitorExit : forall P S,
    PtS c m i = P::S ->
    (PtL c m i) <=l (PtL c m (next_line i)) ->
    S <=s (PtS c m (next_line i)) ->
    PointsTo_instr m i c MonitorExit
  | PT_Run : forall P S,
    PtS c m i = P::S ->
    (PtL c m i) <=l (PtL c m (next_line i)) ->
    (forall h m', P h -> PtCall h run m' -> PtM m' (make_call_context m i c h)) ->
    S <=s (PtS c m (next_line i)) ->
    (forall h m', P h -> PtCall h run m' -> nil <=s (PtS (make_call_context m i c h) m' 0)) ->
    (forall h m', P h -> PtCall h run m' -> PtL (make_call_context m i c h) m' 0 0 h) ->
    PointsTo_instr m i c Run.

  Definition PointsTo_meth (m:method) : Prop :=
    forall c i ins, PtM m c -> body m i = Some ins -> PointsTo_instr m i c ins.

  Inductive PointsTo : Prop :=
    PointsTo_def :
    PtL init_mcontext p.(main) 0 0 init_pcontext ->
    PtM p.(main) init_mcontext ->
    (forall c m, In c p.(classes) -> In m c.(methods) -> PointsTo_meth m) ->
    nil <=s (PtS init_mcontext p.(main) 0) ->
    PointsTo.

  Definition gamma_local (m:method) (i:line) (c:mcontext) (rho:local) : Prop :=
    forall x o, rho x = Loc o -> PtL c m i x (snd o).

  Inductive gamma_list : list (pcontext->Prop) -> list val -> Prop :=
  | gamma_list_nil : gamma_list nil nil
  | gamma_list_cons : forall (P:pcontext->Prop) (S:list (pcontext->Prop)) v s,
    (forall o, v = Loc o -> P (snd o)) ->
    gamma_list S s -> 
    gamma_list (P::S) (v::s).

  Definition gamma_stack (m:method) (i:line) (c:mcontext) (s:op_stack) : Prop :=
    gamma_list (PtS c m i) s.

  Definition gamma_heap (sigma:heap) : Prop :=
    forall o f o' m,
      sigma o = Some m ->
      m f = Loc o' ->
      PtF (snd o) f (snd o').

  Lemma gamma_list_monotone : forall S1 S2,
    S1 <=s S2 -> (gamma_list S1) <= (gamma_list S2).
  Proof.
    unfold incl; induction 1.
    auto.
    intros.
    inv H1; constructor; auto.
  Qed.

  Lemma gamma_local_monotone : forall m i j c,
    (PtL c m i) <=l (PtL c m j) ->
    (gamma_local m i c) <= (gamma_local m j c).
  Proof.
    unfold gamma_local, incl; intros; auto.
    apply H; auto.
  Qed.

  Lemma step0_correct : forall m i c o ppt ins rho sigma rho' i' sigma' s s' a,
    PointsTo_instr m i c ins ->
    step0 o ppt ins (i,s,rho,sigma) (i',s',rho',sigma') a ->
    gamma_heap sigma ->
    gamma_local m i c rho -> 
    gamma_stack m i c s -> 
    gamma_heap sigma' /\ gamma_stack m i' c s' /\ gamma_local m i' c rho'.
  Proof.
    intros m i c o ppt ins rho sigma rho' i' sigma' s s' a HP Hs Gh Gl Gs.
    inv Hs; inv HP; (split; [idtac|split]); auto;
      unfold gamma_stack in *;
    match goal with
      | id : _ <=s _ |- _ => rename id into Hs
    end;
    try match goal with
      | id : _ <=l _ |- _ => rename id into Hl
    end;
    try match goal with
      | id1 : gamma_list ?S1 _, id2 : ?S1=_ |- _ => rewrite id2 in id1
    end;
    repeat match goal with
      | id : gamma_list (_::_) (_::_) |- _ => inv id
    end.
    (* AConstNull *)
    apply gamma_list_monotone with (1:=Hs).
    constructor; auto.
    intros; discriminate.
    apply gamma_local_monotone with (1:=Hl); auto.
    (* ALoad *)
    apply gamma_list_monotone with (1:=Hs).
    constructor; auto.
    apply gamma_local_monotone with (1:=Hl); auto.
    (* Astore *)
    apply gamma_list_monotone with (1:=Hs); auto.
    intros z oz Hz.
    unfold subst in *.
    comp x z; auto.
    apply H1; auto.
    (* GetField *)
    apply gamma_list_monotone with (1:=Hs); constructor; auto.
    destruct HYP2 as [o' [R1 R2]]; intros; subst.
    assert (F:=Gh _ _ _ _ R1 H).
    apply H2 with (2:=F).
    eauto.
    apply gamma_local_monotone with (1:=Hl); auto.
    (* PutField *)
    intros o2 f2 o2' m2 V1 V2.
    destruct HYP2 as [[mo [W1 W2]] W3].
    MLcase o1 o2.
    rewrite V1 in W2; inv W2.
    unfold updateField in V2.
    comp f f2.
    apply (H2 (snd o2)); eauto.
    apply (Gh _ _ _ _ W1 V2).
    rewrite W3 in V1; eauto.
    apply gamma_list_monotone with (1:=Hs); auto.
    apply gamma_local_monotone with (1:=Hl); auto.
    (* Ifnd *)
    apply gamma_list_monotone with (1:=Hs); auto.
    apply gamma_local_monotone with (1:=Hl); auto.
    apply gamma_list_monotone with (1:=H1); auto.
    apply gamma_local_monotone with (1:=H0); auto.
    (* goto *)
    apply gamma_list_monotone with (1:=Hs); auto.
    apply gamma_local_monotone with (1:=Hl); auto.
  Qed.

  Lemma step1_correct : forall o fr fr' a ins,
    step1 o fr fr' a ->
    match fr,fr' with
      (m,i,c,s,rho,sigma),(m',i',c',s',rho',sigma') =>
      body m i = Some ins ->
      PointsTo_instr m i c ins ->
      gamma_heap sigma ->
      gamma_local m i c rho -> 
      gamma_stack m i c s ->
      gamma_heap sigma' /\ gamma_stack m' i' c' s' /\ gamma_local m' i' c' rho'
    end.
  Proof.
    destruct 1; intros Hb HP Gh Gl Gs.
    (* step0 *)
    assert (ins=instr) by congruence; subst.
    eapply step0_correct; eauto.
    (* new *)
    destruct HYP5 as [A1 [A2 A3]].
    rewrite HYP1 in Hb; inv Hb.
    inv HP.
    split; [idtac|split].    
    intros o1 f o1' oo T1 T2.
    destruct (excluded_middle (o1=(a, make_new_context m i cid c))); subst.
    rewrite A2 in T1; inv T1.
    discriminate.
    rewrite A3 in T1; eauto.
    unfold gamma_stack in *.
    apply gamma_list_monotone with (1:=H1); constructor; auto.
    intros.
    inv H.
    unfold singleton; auto.
    apply gamma_local_monotone with (1:=H0); auto.
  Qed.

  Definition PtCall_correct : Prop :=
    forall ms c m' cid,
      get_class p c = Some cid ->
      lookup p ms cid = Some m' ->
      PtCall c ms m'.

  Lemma gamma_list_nth_Null : forall S s,
    gamma_list S s -> forall n o,
    nth n s Null = Loc o ->
    exists P,
      nth_error S n = Some P /\ P (snd o).
  Proof.
    induction 1; simpl; intros.
    destruct n; discriminate.
    destruct n; subst.
    simpl.
    exists P; split; auto.
    elim IHgamma_list with n o; auto.
    intros.
    simpl; destruct H2.
    exists x; split; auto.
  Qed.

  Inductive gamma_cs' : method -> mcontext -> nat -> call_stack -> Prop :=
  | gamma_cs'_nil : forall m c n, gamma_cs' m c n nil
  | gamma_cs'_cons : forall m i c rho s1 o s2 cs cl m1 cid ms,
    In cl (classes p) -> 
    In m (methods cl) -> 
    PtM m c ->

    body m i = Some (InvokeVirtual ms) ->
    get_class p (snd o) = Some cid ->
    lookup p ms cid = Some m1 ->

    gamma_stack m i c (s1++Loc o::s2) ->
    gamma_local m i c rho ->
    gamma_cs' m c (length m.(signature).(args)) cs ->
    gamma_cs' m1 (make_call_context m i c (snd o)) (length s1) ((m,Datatypes.S i,c,s2,rho)::cs).

  Inductive gamma_cs : call_stack -> Prop :=
  | gamma_cs_nil : gamma_cs nil
  | gamma_cs_cons : forall m i c rho s cs cl,
    In cl (classes p) -> 
    In m (methods cl) -> 
    PtM m c ->
    gamma_stack m i c s ->
    gamma_local m i c rho ->
    gamma_cs' m c (length m.(signature).(args)) cs ->
    gamma_cs ((m, i, c, s,rho)::cs).    

  Lemma gamma_list_app : forall S1 S2 s1 s2,
    gamma_list (S1 ++ S2) (s1 ++ s2) ->
    length S1 = length s1 ->
    gamma_list S1 s1 /\ gamma_list S2 s2.
  Proof.
    induction S1; destruct s1; simpl; intros.
    split; auto; constructor.
    discriminate.
    discriminate.
    inv H.
    elim IHS1 with (1:=H6); auto.
    split; auto.
    constructor; auto.
  Qed.

  Definition ValidReturns : Prop :=
    forall c m, 
      In c p.(classes) -> 
      In m c.(methods) ->
      (forall i, body m i = Some Return -> m.(signature).(rtype) = None)
      /\
      forall i, body m i = Some AReturn -> m.(signature).(rtype) <> None.

  Lemma step2_correct : forall o cs cs' sigma sigma' a,
    PointsTo ->
    PtCall_correct ->
    ValidReturns ->
    step2 p o (cs,sigma) (cs',sigma') a ->
    gamma_heap sigma ->
    gamma_cs cs ->    
    gamma_heap sigma' /\ gamma_cs cs'.
  Proof.
    intros o cs cs' sigma sigma' a Hp HCall Hret Hs Hh Hcs.
    inv Hs.
    (* step1 *)
    inv Hcs.
    destruct fr' as [[[[m' i'] c'] s'] rho'].
    assert (exists ins, body m i = Some ins).
    inv H5; eauto.
    destruct H as [ins H].
    destruct (step1_correct _ _ _ _ ins H5); auto.
    inv Hp.
    clear H10.
    apply (H9 _ _ H1 H2); auto.
    split; auto.
    econstructor; intuition eauto.
    inv H5; auto.
    inv H5; auto.
    inv H5; auto.
    (* call *)
    split; auto.
    inv Hcs.
    inv Hp.
    clear H H0 H2.
    assert (HC:=H1 _ _ H8 H13 _ _ _ H14 H4); clear H1.
    inv HC.
    destruct (lookup_prop_1 _ _ _ _ H7) as [C [L1 [L2 [L3 L4]]]]; subst.
    unfold gamma_stack in *.
    rewrite H0 in H15.
    simpl in H1.
    assert (length ARGS = length v_list) by congruence.
    elim gamma_list_app with (1:=H15); auto.
    intros G1 G2; inv G2.
    constructor 2 with C; auto.
    apply H3; auto.
    apply HCall with (cid:=c_name C); auto.
    unfold gamma_stack in *.
    apply gamma_list_monotone with (S1:=@nil (pcontext->Prop)).
    apply H19; auto.
    apply HCall with (cid:=c_name C); auto.
    constructor.
    intros z oz Hz.
    destruct z.
    assert (o'=oz) by congruence; subst.
    apply H20; auto.
    apply HCall with (cid:=c_name C); auto.
    destruct (le_gt_dec (Datatypes.S z) (length args)).
    rewrite H10 in Hz; try omega.
    simpl in H21.
    elim (gamma_list_nth_Null _ _ G1) with (1:=Hz).
    intros Q [B1 B2].
    apply (H21 (snd o')) with Q; auto.
    apply HCall with (cid:=c_name C); auto.
    rewrite H11 in Hz; try discriminate; omega.

    replace (length (prog_syntax.args (signature m1))) with (length v_list).
    constructor 2 with cl (c_name C) (signature m1); auto.
    rewrite L4; auto.
    rewrite L4; auto.
    unfold gamma_stack in *.
    rewrite H0; auto.
    rewrite L4; auto.
    (* return *)
    split; auto.
    inv Hcs.
    inv Hp.
    clear H2.
    inv H11.
    constructor.
    destruct (lookup_prop_1 _ _ _ _ H15) as [C [L1 [L2 [L3 L4]]]].
    subst.
    assert (Hc:=H1 _ _ H3 H4 _ _ _ H12 H13).
    inv Hc.
    constructor 2 with cl0; auto.
    unfold gamma_stack in *.
    destruct (Hret _ _ H6 H7).
    apply gamma_list_monotone with (1:=(H23 (H11 _ H5))).
    rewrite H18 in H16.
    elim gamma_list_app with (1:=H16); auto.
    intros.
    inv H30; auto.
    congruence.
    apply gamma_local_monotone with (1:=H21); auto.
    (* Areturn *)
    split; auto.
    inv Hcs.
    inv Hp.
    clear H2.
    inv H11.
    destruct (lookup_prop_1 _ _ _ _ H23) as [C [L1 [L2 [L3 L4]]]].
    subst.
    assert (Hc:=H1 _ _ H6 H7 _ _ _ H8 H5).
    inv Hc.
    assert (Hc:=H1 _ _ H16 H17 _ _ _ H20 H21).
    inv Hc.
    constructor 2 with cl0; auto.
    unfold gamma_stack in *.
    destruct (Hret _ _ H6 H7).
    apply gamma_list_monotone with (1:=(H19 (H30 _ H5))).
    rewrite H12 in H24.
    elim gamma_list_app with (1:=H24); auto.
    intros.
    inv H32; auto.
    constructor; auto.
    intros.
    subst.
    rewrite H3 in H9.
    inv H9.
    exists (snd o0); exists m; split; auto.
    split; auto.
    apply HCall with (cid:=c_name C); auto.
    congruence.
    apply gamma_local_monotone with (1:=H14); auto.
  Qed.

  Definition gamma_thread (L:threads) : Prop :=
    forall o cs, L o = Some cs -> gamma_cs cs. 

  Lemma gamma_thread_upd : forall L o cs,
    gamma_thread L ->
    gamma_cs cs ->
    gamma_thread (upd_thread L o cs).
  Proof.
    intros.
    unfold upd_thread.
    intros o0 cs0 T.
    MLcase' o o0.
    inv T; auto.
    eapply H; eauto.
  Qed.
  Hint Resolve gamma_thread_upd.

  Lemma step3_correct : forall L o cs sigma mu L' sigma' mu' a,
    PointsTo ->
    PtCall_correct ->
    ValidReturns ->
    step3 p L (o,cs,sigma,mu) (L',sigma',mu') a ->
    gamma_thread L ->
    gamma_cs cs ->
    gamma_heap sigma ->
    gamma_heap sigma' /\ gamma_thread L'.
  Proof.
    intros L o cs sigma mu L' sigma' mu' a Hp HCall Hret Hs Ht Hcs Hh.
    inv Hs.
    (* step2 *)
    elim step2_correct with (4:=H8); auto.
    (* run *)
    inv Hcs.
    inv Hp.
    clear H2.
    assert (HC:=H1 _ _ H5 H6 _ _ _ H7 H8).
    inv HC.
    split; auto.
    apply gamma_thread_upd.
    apply gamma_thread_upd.
    auto.
    econstructor; eauto; unfold gamma_stack in *.
    rewrite H2 in H11.
    inv H11.
    apply gamma_list_monotone with (1:=H17); auto.
    apply gamma_local_monotone with (1:=H3); auto.
    destruct (lookup_prop_1 _ _ _ _ H10) as [C T].
    decompose [and] T; subst; clear T.
    unfold gamma_stack in *; rewrite H2 in H11; inv H11.
    constructor 2 with C; auto.
    apply H4; auto.
    apply HCall with (cid:=c_name C); auto.
    unfold gamma_stack.
    apply (gamma_list_monotone nil).
    apply H18; auto.
    apply HCall with (cid:=c_name C); auto.
    constructor.
    intros z oz Hz.
    destruct z.
    replace oz with o' in * by congruence.
    apply H19; auto.
    apply HCall with (cid:=c_name C); auto.
    rewrite H13 in Hz; discriminate.
    constructor.
    (* MonitorEnter *)
    inv Hp.
    clear H2.
    inv Hcs.
    assert (HC:=H1 _ _ H10 H11 _ _ _ H12 H8).
    inv HC.
    split; auto.
    intros z oz Hz.
    unfold upd_thread in *.
    MLcase' o z.
    inv Hz.
    constructor 2 with cl; auto.
    unfold gamma_stack in *.
    rewrite H2 in H13; inv H13.
    apply gamma_list_monotone with (1:=H4); auto.
    apply gamma_local_monotone with (1:=H3); auto.
    apply (Ht _ _ Hz).
    (* MonitorExit *)
    inv Hp.
    clear H2.
    inv Hcs.
    assert (HC:=H1 _ _ H10 H11 _ _ _ H12 H8).
    inv HC.
    split; auto.
    intros z oz Hz.
    unfold upd_thread in *.
    MLcase' o z.
    inv Hz.
    constructor 2 with cl; auto.
    unfold gamma_stack in *.
    rewrite H2 in H13; inv H13.
    apply gamma_list_monotone with (1:=H4); auto.
    apply gamma_local_monotone with (1:=H3); auto.
    apply (Ht _ _ Hz).
  Qed.

  Lemma step_correct : forall L sigma mu L' sigma' mu' a,
    PointsTo ->
    PtCall_correct ->
    ValidReturns ->
    step p (L,sigma,mu) (L',sigma',mu') a ->
    gamma_heap sigma ->
    gamma_thread L ->
    gamma_heap sigma' /\ gamma_thread L'.
  Proof.
    intros L sigma mu L' sigma' mu' a Hp HCall Hv Hs Hg Ht.
    inv Hs.
    elim step3_correct with (4:=H6); eauto.
  Qed.

  Definition MayTarget (ppt:PPT) : (pcontext -> Prop) :=
    match ppt with
      (m,i,c) => match body m i with
                   | None => fun _ => False
                   | Some ins => 
                     match ins with
                       | GetField f => match PtS c m i with
                                         | P::_ => P
                                     | _ => (fun _ => False)
                                       end
                       | PutField f => match PtS c m i with
                                         | _::P::_ => P
                                         | _ => (fun _ => False)
                                       end
                       | _ => fun _ => False
                     end
                 end
    end.

  Lemma MayTarget_correct : forall p L sigma mu st' a ppt o,
    step p (L,sigma,mu) st' a ->
    get_ppt ppt a ->
    get_target o a -> 
    gamma_thread L ->
    MayTarget ppt (snd o).
  Proof.
    intros.
    inv H; inv H0; inv H1.
    assert (V:=H2 _ _ H9).
    inv V.
    inv H8.
    inv H17.
    inv H14.
    inv HYP2.
    unfold MayTarget; rewrite HYP1.
    inv H5.
    eauto.
    unfold MayTarget; rewrite HYP1.
    inv H5.
    inv H11.
    eauto.
  Qed.

End PointsTo.

  Lemma reachable_correct' : forall p st PtV PtS PtF PtR PtM PtCall,
    PointsTo p PtV PtS PtF PtR PtM PtCall  ->
    PtCall_correct p PtCall ->
    ValidReturns p ->
    reachable p st ->
    match st with (L,sigma,mu) =>
      gamma_heap PtF sigma /\ gamma_thread p PtV PtS PtM L
    end.
  Proof.
    induction 4.
    destruct H.
    unfold init.
    unfold sigma_init, threads_init; split.
    repeat intro.
    MLcase o (run_address, init_p p); try discriminate.
    inv H5; discriminate.
    repeat intro.
    destruct eq_memloc'; try discriminate.
    inv H5.
    constructor 2 with p.(main_class).
    apply main_class_prop.
    apply main_prop_1.
    auto.
    unfold gamma_stack.
    apply gamma_list_monotone with (1:=H4).
    constructor.
    repeat intro; discriminate.
    constructor.
    destruct st as [[L sigma]mu].
    destruct st' as [[L' sigma']mu'].
    destruct IHreachable; auto.
    eapply step_correct; eauto.
  Qed.

  Lemma MayTarget_reachable_correct' : forall p PtV PtS PtF PtR PtM PtCall L sigma mu st' a o ppt,
    PointsTo p PtV PtS PtF PtR PtM PtCall  ->
    PtCall_correct p PtCall ->
    ValidReturns p ->
    reachable p (L,sigma,mu) ->
    step p (L,sigma,mu) st' a ->
    get_ppt ppt a ->
    get_target o a -> 
    MayTarget PtS ppt (snd o).
  Proof.
    intros; eapply MayTarget_correct; eauto.
    destruct (reachable_correct' p (L,sigma,mu) PtV PtS PtF PtR PtM PtCall); eauto.
  Qed.

  Definition PtCall_bool (p:program) (c:pcontext) (ms:method_signature) (m':method) : bool :=
    match get_class p c with
      | Some cid =>  
        match lookup p ms cid with
          | Some m'' => if eq_method m' m'' then true else false
          | None => false
        end
      | None => false
    end.
  
  Lemma PtCall_bool_correct : forall p,
    PtCall_correct p (fun c ms m' => PtCall_bool p c ms m' = true).
  Proof.
    repeat intro.
    unfold PtCall_bool; rewrite H; rewrite H0.
    comp m' m'; intuition.
  Qed.

  Record pt : Type := make_PT {
    ptL: mcontext -> method -> line -> var -> pcontext -> Prop;
    ptS: mcontext -> method -> line -> list (pcontext -> Prop);
    ptF: pcontext -> field -> pcontext -> Prop;
    ptR : mcontext -> method -> pcontext -> Prop;
    ptM : method -> mcontext -> Prop
  }.

  Definition PointsToSpec (p:program) (PT:pt) : Prop :=
    match PT with
      make_PT PtV PtS PtF PtR PtM =>
      PointsTo p PtV PtS PtF PtR PtM (fun c ms m' => PtCall_bool p c ms m' = true)
    end.

  Lemma reachable_correct : forall p st PT,
    PointsToSpec p PT ->
    ValidReturns p ->
    reachable p st ->
    match st with (L,sigma,mu) =>
      gamma_heap PT.(ptF) sigma /\ gamma_thread p PT.(ptL) PT.(ptS) PT.(ptM) L
    end.
  Proof.
    intros.
    destruct PT; simpl in H.
    simpl.
    eapply reachable_correct'; eauto.
    apply PtCall_bool_correct.
  Qed.

  Lemma MayTarget_reachable_correct : forall p PT L sigma mu st' a o ppt,
    PointsToSpec p PT ->
    ValidReturns p ->
    reachable p (L,sigma,mu) ->
    step p (L,sigma,mu) st' a ->
    get_ppt ppt a ->
    get_target o a -> 
    MayTarget PT.(ptS) ppt (snd o).
  Proof.
    intros.
    destruct PT; simpl in *.
    eapply MayTarget_reachable_correct'; eauto.
    apply PtCall_bool_correct.
  Qed.

End MakePointsTo.

