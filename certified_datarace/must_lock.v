Require Export FSets.
Require Export sem_inv.

Module MakeMustLock (S:SEMANTIC).

  Import S C.

  Ltac MLcase x y := destruct (eq_memloc x y); [subst|idtac].
  Ltac MLcase' x y := destruct (eq_memloc' x y); [subst|idtac].

  Module I := SemInv S.


Section MustLock.

  Inductive expr' : Set := Var (x:var) | Field (e:expr') (f:field).
  Inductive expr : Set := Top | E (e:expr').
  Coercion E : expr' >-> expr.

  Definition order_expr (e1 e2 : expr) : Prop :=
    match e1 with
      | Top => e2=Top
      | E e1 => e2=E e1 \/ e2=Top
    end.
  Notation "e1 <= e2" := (order_expr e1 e2).

  Inductive order_stack : list expr -> list expr -> Prop :=
  | order_stack_nil : order_stack nil nil
  | order_stack_cons : forall e1 e2 s1 s2, 
    e1 <= e2 -> order_stack s1 s2 -> order_stack (e1::s1) (e2::s2).
  Notation "s1 <=s s2" := (order_stack s1 s2) (at level 50).

  Definition order_lock (l1 l2 : var->Prop) : Prop :=
    forall x, l2 x -> l1 x.
  Notation "l1 <=l l2" := (order_lock l1 l2) (at level 50).

  Variable p : program.
  Variable PtL : mcontext -> method -> line -> var -> pcontext -> Prop.
  Variable Locks: mcontext -> method -> line -> var -> Prop.
  Variable S: mcontext -> method -> line -> list expr.

  Inductive MustLock_instr (c:mcontext) (m:method) (i:line) : instruction -> Prop :=
  | ML_AconstNull : 
    (Locks c m i) <=l (Locks c m (next_line i)) ->
    (Top::(S c m i)) <=s (S c m (next_line i)) ->
    MustLock_instr c m i AConstNull
  | ML_New : forall cl,
    (Locks c m i) <=l (Locks c m (next_line i)) ->
    (Top::(S c m i)) <=s (S c m (next_line i)) ->
    MustLock_instr c m i (New cl)
  | ML_ALoad : forall x,
    (Locks c m i) <=l (Locks c m (next_line i)) ->
    ((E (Var x))::(S c m i)) <=s (S c m (next_line i)) ->
    MustLock_instr c m i (ALoad x)
  | ML_AStore : forall x e s,
    S c m i = e::s ->
    (fun y => Locks c m i y /\ x<>y) <=l (Locks c m (next_line i)) ->
    (List.map (fun _ => Top) s) <=s (S c m (next_line i)) ->
    MustLock_instr c m i (AStore x)
  | ML_GetField : forall f e s,
    S c m i = e::s ->
    (Locks c m i) <=l (Locks c m (next_line i)) ->
    ((match e with Top => Top | E e => E (Field e f) end)::s) <=s (S c m (next_line i)) ->
    MustLock_instr c m i (GetField f)
  | ML_PutField : forall f e1 e2 s,
    S c m i = e1::e2::s ->
    (Locks c m i) <=l (Locks c m (next_line i)) ->
    (List.map (fun _ => Top) s) <=s (S c m (next_line i)) ->
    MustLock_instr c m i (PutField f)
  | ML_Ifnd : forall j,
    (S c m i) <=s (S c m (next_line i)) ->
    (S c m i) <=s (S c m j) ->
    (Locks c m i) <=l (Locks c m (next_line i)) ->
    (Locks c m i) <=l (Locks c m j) ->
    MustLock_instr c m i (Ifnd j)
  | ML_Goto : forall j,
    (S c m i) <=s (S c m j) ->
    (Locks c m i) <=l (Locks c m j) ->
    MustLock_instr c m i (Goto j)
  | ML_InvokeVirtual : forall ms ARGS e s,
    S c m i = ARGS++e::s ->
    length ARGS = length ms.(args) ->
    (ms.(rtype) = None -> (List.map (fun _=> Top) s) <=s (S c m (next_line i))) ->
    (ms.(rtype) <> None -> (Top::(List.map (fun _=> Top) s)) <=s (S c m (next_line i))) ->
    (fun _ => False) <=l (Locks c m (next_line i)) ->
    MustLock_instr c m i (InvokeVirtual ms)
  | ML_AReturn : 
    MustLock_instr c m i AReturn
  | ML_MonitorEnter : forall e s,
    S c m i = e::s ->
    s <=s (S c m (next_line i)) ->
    (match e with
       | E (Var x) => (fun y => y=x \/ Locks c m i y) <=l (Locks c m (next_line i)) 
       | _ => (Locks c m i) <=l (Locks c m (next_line i))
     end) ->
    MustLock_instr c m i MonitorEnter
  | ML_MonitorExit : forall e s,
    S c m i = e::s ->
    s <=s (S c m (next_line i)) ->
     (match e with
       | E (Var x) => (fun y => Locks c m i y /\ ~ (exists h, PtL c m i y h /\ PtL c m i x h)) <=l (Locks c m (next_line i)) 
       | _ => (fun _ => False) <=l (Locks c m (next_line i))
     end) ->
    MustLock_instr c m i MonitorExit
  | ML_Run : forall e s,
    S c m i = e::s ->
    s <=s (S c m (next_line i)) ->
    (Locks c m i) <=l (Locks c m (next_line i)) ->
    MustLock_instr c m i Run.

  Definition MustLock_meth (m:method) (c:mcontext) : Prop :=
    forall i ins, body m i = Some ins -> MustLock_instr c m i ins.

  Definition MustLock (cg:method->mcontext->Prop) : Prop :=
    forall cl m,
      In cl p.(classes) -> 
      In m cl.(methods) -> 
      forall c, cg m c ->
      (nil <=s (S c m 0) /\ (fun _ => False) <=l (Locks c m 0))  /\
      forall i ins, 
        body m i = Some ins -> 
        MustLock_instr c m i ins.

  Definition gamma_locks (c:mcontext) (m:method) (i:line) (l:local) (mu:lock) (ot:location) : Prop := 
    forall x, Locks c m i x ->
      exists o, l x = Loc o /\ exists n, mu (fst o) = Held ot n.

  Inductive gamma_expr' (l:local) (ls:list heap) : expr' -> val -> Prop :=
  | gamma_expr'_var : forall x, gamma_expr' l ls (Var x) (l x)
  | gamma_expr'_field : forall e f o m sigma,
    In sigma ls ->
    gamma_expr' l ls e (Loc o) ->
    sigma o = Some m ->
    gamma_expr' l ls (Field e f) (m f).

  Inductive gamma_expr (l:local) (ls:list heap) : expr -> val -> Prop :=
  | gamma_expr_top : forall v, gamma_expr l ls Top v
  | gamma_expr_E : forall e v, gamma_expr' l ls e v -> gamma_expr l ls (E e) v.      

  Inductive gamma_list (l:local) (ls:list heap) : list expr -> list val -> Prop :=
  | gamma_list_nil : gamma_list l ls nil nil
  | gamma_list_cons : forall E S  v s,
    gamma_expr l ls E v ->
    gamma_list l ls S s -> 
    gamma_list l ls (E::S) (v::s).

  Definition gamma_stack (c:mcontext) (m:method) (i:line) (s:op_stack)  (l:local) (lsigma: list heap) : Prop :=
    gamma_list l lsigma (S c m i) s.

  Lemma gamma_expr_monotone : forall E1 E2 v l ls,
    E1 <= E2 -> 
    gamma_expr l ls E1 v ->
    gamma_expr l ls E2 v.
  Proof.
    destruct E1; simpl; intros.
    subst; constructor.
    destruct H; subst; constructor.
    inv H0; auto.
  Qed.

  Lemma gamma_list_monotone : forall S1 S2 l lsigma,
    S1 <=s S2 -> forall s,
    gamma_list l lsigma S1 s ->
    gamma_list l lsigma S2 s.
  Proof.
    induction 1.
    auto.
    intros.
    inv H1; econstructor; eauto.
    eapply gamma_expr_monotone; eauto.
  Qed.

  Lemma gamma_exp'_monotone_cons : forall E l ls v,
    gamma_expr' l ls E v -> forall sigma,
    gamma_expr' l (sigma::ls) E v.
  Proof.
    induction 1.
    constructor.
    intros.
    constructor 2 with o sigma; auto with datatypes.
  Qed.

  Lemma gamma_expr_monotone_cons : forall E l ls v,
    gamma_expr l ls E v -> forall sigma,
    gamma_expr l (sigma::ls) E v.
  Proof.
    intros.
    inv H; constructor.
    eapply gamma_exp'_monotone_cons; eauto.
  Qed.

  Lemma gamma_list_monotone_cons : forall S l ls s,
    gamma_list l ls S s -> forall sigma,
    gamma_list l (sigma::ls) S s.
  Proof.
    induction 1.
    constructor.
    intros.
    constructor; auto.
    inv H; constructor.
    eapply gamma_exp'_monotone_cons; eauto.
  Qed.
  Hint Resolve gamma_list_monotone_cons gamma_exp'_monotone_cons gamma_expr_monotone_cons.

  Lemma gamma_list_length : forall S1 l sigma s,
    gamma_list l sigma S1 s -> length S1 = length s.
  Proof.
    induction 1; auto.
    simpl; congruence.
  Qed.

  Lemma gamma_list_top : forall S1 l lsigma s,
    length S1 = length s ->
    gamma_list l lsigma (List.map (fun _:expr => Top) S1) s.
  Proof.
    induction S1; destruct s; simpl; intuition; try constructor.
    discriminate.
    discriminate.
    simpl; repeat econstructor; eauto.
    eapply IHS1.
    congruence.
  Qed.

  Lemma gamma_lock_monotone : forall m i j c,
    (Locks c m i) <=l (Locks c m j) -> forall l mu o,
    gamma_locks c m i l mu o ->
    gamma_locks c m j l mu o.
  Proof.
    unfold gamma_locks; intros; auto.
  Qed.

  Lemma step0_correct : forall c m i o ppt ins rho sigma rho' i' sigma' s s' a mu ls,
    MustLock_instr c m i ins ->
    step0 o ppt ins (i,s,rho,sigma) (i',s',rho',sigma') a ->
    gamma_locks c m i rho mu (fst o) -> 
    gamma_stack c m i s rho ls -> 
    gamma_stack c m i' s' rho' (sigma'::ls) /\ gamma_locks c m i' rho' mu (fst o).
  Proof.
    intros c m i o ppt ins rho sigma rho' i' sigma' s s' a mu ls HP Hs Gl Gs.
    inv Hs; inv HP; split; auto;
      unfold gamma_stack in *;
    match goal with
      | id : _ <=s _ |- _ => rename id into Hs
    end;
    try match goal with
      | id : _ <=l _ |- _ => rename id into Hl
    end;
    try match goal with
      | id1 : gamma_list _ _ ?S1 _, id2 : ?S1=_ |- _ => rewrite id2 in id1
    end;
    repeat match goal with
      | id : gamma_list _ _ (_::_) (_::_) |- _ => inv id
    end.
    (* AConstNull *)
    apply gamma_list_monotone with (1:=Hs).
    constructor; auto with datatypes.
    constructor.
    apply gamma_lock_monotone with (1:=Hl); auto.
    (* ALoad *)
    apply gamma_list_monotone with (1:=Hs).
    constructor; auto with datatypes.
    repeat constructor.
    apply gamma_lock_monotone with (1:=Hl); auto.
    (* Astore *)
    apply gamma_list_monotone with (1:=Hs); auto.
    apply gamma_list_top.
    elim gamma_list_length with (1:=H5); auto.
    intros y Hy.
    assert (V:=Hl _ Hy).
    unfold subst.
    destruct (eq_var x y); subst.
    intuition.
    apply Gl.
    destruct V; auto.
    (* GetField *)
    apply gamma_list_monotone with (1:=Hs); try constructor; auto.
    destruct e.
    constructor.
    destruct HYP2 as [mm [T1 T2]].
    rewrite <- T2.
    inv H3; constructor.
    constructor 2 with o1 sigma'; auto with datatypes.
    apply gamma_lock_monotone with (1:=Hl); auto.
    (* PutField *)
    apply gamma_list_monotone with (1:=Hs); auto.
    apply gamma_list_top.
    elim gamma_list_length with (1:=H7); auto.
    apply gamma_lock_monotone with (1:=Hl); auto.
    (* Ifnd *)
    apply gamma_list_monotone with (1:=Hs); auto.
    apply gamma_lock_monotone with (1:=Hl); auto.
    apply gamma_list_monotone with (1:=H0); auto.
    apply gamma_lock_monotone with (1:=H2); auto.
    (* goto *)
    apply gamma_list_monotone with (1:=Hs); auto.
    apply gamma_lock_monotone with (1:=Hl); auto.
  Qed.

  Lemma step1_correct : forall o fr fr' a ins mu ls,
    step1 o fr fr' a ->
    match fr,fr' with
      (m,i,c,s,rho,sigma),(m',i',c',s',rho',sigma') =>
      body m i = Some ins ->
      MustLock_instr c m i ins ->
      gamma_locks c m i rho mu (fst o) -> 
      gamma_stack c m i s rho ls ->
      gamma_stack c' m' i' s' rho' (sigma'::ls) /\ gamma_locks c' m' i' rho' mu (fst o)
    end.
  Proof.
    destruct 1; intros Hb HP Gl Gs.
    (* step0 *)
    assert (ins=instr) by congruence; subst.
    eapply step0_correct; eauto.
    (* new *)
    replace ins with (New cid) in * by congruence.
    inv HP.
    split.
    unfold gamma_stack in *.
    apply gamma_list_monotone with (1:=H1); constructor; auto.
    constructor.
    apply gamma_lock_monotone with (1:=H0); auto.
  Qed.

  Lemma gamma_list_app : forall S1 S2 s1 s2 l sigma,
    gamma_list l sigma (S1 ++ S2) (s1 ++ s2) ->
    length S1 = length s1 ->
    gamma_list  l sigma S1 s1  /\ gamma_list  l sigma S2 s2 .
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

  Lemma gamma_locks_acquire : forall o o' mu mu' c m i rho ot,
    acquire o o' mu mu' -> ot <> o ->
    gamma_locks c m i rho mu ot ->
    gamma_locks c m i rho mu' ot.
  Proof.
    unfold gamma_locks; intros.
    destruct H.
    destruct (H1 _ H2) as [o'' [T1 [n T2]]]; clear H1.
    exists o''; split; auto.
    destruct (eq_pos (fst o'') o'); subst.
    destruct H3.
    intuition; congruence.
    destruct H1; intuition eauto.
    exists (Datatypes.S x0); congruence.
    rewrite H; eauto.
  Qed.

  Lemma gamma_locks_release : forall o o' mu mu' c m i rho ot,
    release o o' mu mu' -> ot <> o ->
    gamma_locks c m i rho mu ot ->
    gamma_locks c m i rho mu' ot.
  Proof.
    unfold gamma_locks; intros.
    destruct H.
    destruct (H1 _ H2) as [o'' [T1 [n T2]]]; clear H1.
    exists o''; split; auto.
    destruct (eq_pos (fst o'') o'); subst.
    destruct H3.
    intuition; congruence.
    destruct H1; intuition eauto.
    exists (Datatypes.S x0); congruence.
    rewrite H; eauto.
  Qed.


  Inductive gamma_cs' : method -> nat -> call_stack -> Prop :=
  | gamma_cs'_nil : forall m n, gamma_cs' m n nil
  | gamma_cs'_cons : forall m i rho s1 o s2 cs cl m1 ms c sigma,
    In cl (classes p) -> 
    In m (methods cl) -> 

    body m i = Some (InvokeVirtual ms) ->

    ms = m1.(signature) ->
    gamma_stack c m i (s1++Loc o::s2) rho sigma ->
    gamma_cs' m (length m.(signature).(args)) cs ->
    gamma_cs' m1 (length s1) ((m,Datatypes.S i,c,s2,rho)::cs).

  Inductive gamma_cs (o:location) (mu:lock) (ls:list heap) : call_stack -> Prop :=
  | gamma_cs_nil : gamma_cs o mu ls nil
  | gamma_cs_cons : forall m i rho s cs cl c,
    In cl (classes p) -> 
    In m (methods cl) -> 
    gamma_stack c m i s rho ls ->
    gamma_locks c m i rho mu o ->
    gamma_cs' m (length m.(signature).(args)) cs ->
    gamma_cs o mu ls ((m, i, c, s,rho)::cs).

  Lemma gamma_cs_acquire : forall o o' mu mu' sigma cs ot,
    acquire o o' mu mu' -> ot <> o ->
    gamma_cs ot mu sigma cs ->
    gamma_cs ot mu' sigma cs.
  Proof.
    intros.
    inv H1; econstructor; eauto.
    eapply gamma_locks_acquire; eauto.
  Qed.

  Lemma gamma_cs_release : forall o o' mu mu' sigma cs ot,
    release o o' mu mu' -> ot <> o ->
    gamma_cs ot mu sigma cs ->
    gamma_cs ot mu' sigma cs.
  Proof.
    intros.
    inv H1; econstructor; eauto.
    eapply gamma_locks_release; eauto.
  Qed.

  Definition ValidReturns : Prop :=
    forall c m, 
      In c p.(classes) -> 
      In m c.(methods) ->
      (forall i, body m i = Some Return -> m.(signature).(rtype) = None)
      /\
      forall i, body m i = Some AReturn -> m.(signature).(rtype) <> None.

  Lemma step2_correct : forall cg o cs cs' sigma sigma' a mu ls,
    MustLock cg ->
    ValidReturns ->
    (forall c m i s rho, In (m, i, c, s, rho) cs -> cg m c) ->
    (forall c m i s rho, In (m, i, c, s, rho) cs' -> cg m c) ->
    step2 p o (cs,sigma) (cs',sigma') a ->
    gamma_cs (fst o) mu ls cs -> gamma_cs (fst o) mu (sigma'::ls) cs'.
  Proof.
    intros cg o cs cs' sigma sigma' a mu ls Hp HR Hi Hi' Hs Hcs.
    inv Hs.
    (* step1 *)
    inv Hcs.
    destruct fr' as [[[[m' i'] c'] s'] rho'].
    assert (exists ins, body m i = Some ins).
    inv H5; eauto.
    destruct H as [ins H].
    destruct (step1_correct _ _ _ _ ins mu ls H5); eauto.
    destruct (Hp _ _ H1 H2 c); eauto with datatypes.
    econstructor; intuition eauto.
    inv H5; auto.
    inv H5; auto.
    (* call *)
    inv Hcs.
    destruct (Hp _ _ H6 H13 c); eauto with datatypes.
    assert (HC:=H0 _ _ H4).
    inv HC.
    destruct (lookup_prop_1 _ _ _ _ H7) as [C [L1 [L2 [L3 L4]]]]; subst.
    unfold gamma_stack in *.
    rewrite H2 in H14.
    simpl in *.
    assert (length ARGS = length v_list) by congruence.
    elim gamma_list_app with (1:=H14); auto.
    intros G1 G2; inv G2.
    constructor 2 with C; auto.
    destruct (Hp _ _ L1 L3 (make_call_context m i c (snd o'))) as [[P _] _];
      eauto with datatypes.
    unfold gamma_stack in *.
    apply gamma_list_monotone with (1:=P); constructor.
    destruct (Hp _ _ L1 L3 (make_call_context m i c (snd o'))) as [[_ P] _]; eauto with datatypes.
    repeat intro.
    assert (E:=P _ H19).
    elim E.

    replace (length (prog_syntax.args (signature m1))) with (length v_list).
    constructor 2 with o' cl (signature m1) ls; auto.
    rewrite L4; auto.
    unfold gamma_stack in *.
    rewrite H2; auto.
    rewrite L4; auto.
    (* return *)
    inv Hcs.
    inv H10.
    constructor.
    destruct (Hp _ _ H0 H1 c0) as [_ P]; eauto with datatypes.
    assert (Q:=P _ _ H2).
    inv Q.
    constructor 2 with cl0; auto.
    unfold gamma_stack in *.
    destruct (HR _ _ H4 H7) as [R _].
    apply gamma_list_monotone with (1:=H13 (R _ H5)).
    apply gamma_list_top.
    rewrite H10 in H6.
    elim gamma_list_app with (1:=H6); auto.
    intros.
    inv H16; auto.
    eapply gamma_list_length; eauto.
    simpl in *; congruence.
    repeat intro.
    assert (V:=H15 _ H3).
    elim V.
    (* Areturn *)
    inv Hcs.
    inv H10.
    destruct (Hp _ _ H13 H14 c') as [_ P]; eauto with datatypes.
    assert (Q:=P _ _ H15).
    inv Q.
    constructor 2 with cl0; auto.
    unfold gamma_stack in *.
    destruct (HR _ _ H4 H7) as [_ R].
    apply gamma_list_monotone with (1:=H6 (R _ H5)).
    constructor.
    constructor.
    apply gamma_list_top.
    rewrite H1 in H17.
    elim gamma_list_app with (1:=H17); auto.
    intros.
    inv H11; auto.
    eapply gamma_list_length; eauto.
    simpl in *; congruence.
    repeat intro.
    assert (V:=H10 _ H0).
    elim V.
  Qed.

  Definition gamma_thread (mu:lock) (ls:list heap) (L:threads) : Prop :=
    forall o cs, L o = Some cs -> gamma_cs (fst o) mu ls cs. 

  Lemma gamma_thread_upd : forall L o mu ls cs,
    gamma_thread mu ls L ->
    gamma_cs (fst o) mu ls cs ->
    gamma_thread mu ls (upd_thread L o cs).
  Proof.
    intros.
    unfold upd_thread.
    intros o0 cs0 T.
    MLcase' o o0.
    inv T; auto.
    eapply H; eauto.
  Qed.
  Hint Resolve gamma_thread_upd.

  Lemma gamma_cs_monotone_cons : forall o mu ls cs,
    gamma_cs o mu ls cs -> forall sigma, gamma_cs o mu (sigma::ls) cs.
  Proof.
    induction 1; econstructor; eauto.
    unfold gamma_stack in *; auto.
  Qed.

  Lemma gamma_thread_monotone_cons : forall mu ls L,
    gamma_thread mu ls L -> forall sigma,  gamma_thread mu (sigma::ls) L.
  Proof.
    repeat intro.
    apply gamma_cs_monotone_cons; eauto.
  Qed.
  Hint Resolve gamma_thread_monotone_cons.

  Lemma step3_correct : forall cg L o cs sigma mu L' sigma' mu' a ls,
    MustLock cg ->
    ValidReturns ->
    (forall c m i s rho, In (m, i, c, s, rho) cs -> cg m c) ->
    (forall o cs c m i s rho, L' o = Some cs -> In (m, i, c, s, rho) cs -> cg m c) ->
    (forall o cs c m i s rho o' x, L o = Some ((m, i, c, s, rho)::cs) ->
      rho x = Loc o' -> PtL c m i x (snd o')) ->
    (forall z, fst z = fst o -> L z <> None -> o = z) ->
    (forall o cs c m i s rho, L o = Some cs -> In (m, i, c, s, rho) cs -> 
      forall x x' o o', rho x = Loc o -> rho x' = Loc o' -> fst o = fst o' -> o = o') ->
    step3 p L (o,cs,sigma,mu) (L',sigma',mu') a ->
    L o = Some cs ->
    gamma_thread mu ls L ->
    gamma_cs (fst o) mu ls cs ->
    gamma_thread mu' (sigma'::ls) L'.
  Proof.
    intros cg L o cs sigma mu L' sigma' mu' a ls Hp Hret Hi Hi' HPtL HL Hrho Hs HLcs Ht Hcs.
    inv Hs.
    (* step2 *)
    assert (gamma_cs (fst o) mu' (sigma'::ls) cs').
    eapply step2_correct; eauto.
    intros; eapply (Hi' o cs'); eauto.
    unfold upd_thread.
    destruct (eq_memloc' o o); intuition.    
    apply gamma_thread_upd; auto.
    
    (* run *)
    inv Hcs.
    destruct (Hp _ _ H4 H6 c) as [_ Hp3].
    eauto with datatypes.
    assert (HC:=Hp3 _ _ H8); clear Hp3.
    inv HC.
    apply gamma_thread_upd.
    apply gamma_thread_upd.
    auto.
    econstructor; eauto; unfold gamma_stack in *.
    rewrite H in H7.
    inv H7.
    apply gamma_list_monotone with (1:=H0); auto.
    apply gamma_lock_monotone with (1:=H1); auto.
    destruct (lookup_prop_1 _ _ _ _ H10) as [C T].
    decompose [and] T; subst; clear T.
    destruct (Hp _ _ H2 H3 ( make_call_context m i c (snd o'))) as [[Hp1 Hp2] _].
    eapply (Hi' (fst o', Some (snd o'))); eauto with datatypes.
    unfold upd_thread.
    destruct eq_memloc'.
    eauto.
    intuition.
    constructor 2 with C; auto.
    unfold gamma_stack in *.
    apply gamma_list_monotone with (1:=Hp1); auto.
    constructor.
    repeat intro.
    assert (V:=Hp2 _ H5).
    elim V.
    constructor.
    (* MonitorEnter *)
    inv Hcs.
    destruct (Hp _ _ H4 H6 c) as [_ Hp3].
    eauto with datatypes.
    assert (HC:=Hp3 _ _ H8).
    inv HC; clear Hp3.
    intros z cs Hz.
    unfold upd_thread in *.
    MLcase' o z.
    inv Hz.
    constructor 2 with cl; auto.
    unfold gamma_stack in *.
    rewrite H in H7; inv H7.
    apply gamma_list_monotone with (1:=H0); auto.
    unfold gamma_stack in *.
    rewrite H in H7; inv H7.
    inv H12.
    intros x Hx.
    destruct (H10 x); auto.
    destruct H2.
    destruct H9.
    destruct (excluded_middle (fst x0 = fst o')).
    destruct H7.
    destruct H3.
    destruct H7; congruence.
    destruct H7 as [n [T1 T2]].
    exists x0; split; auto.
    destruct H3 as [nn H3].
    exists (Datatypes.S n); congruence.
    rewrite <- H5 in H3; eauto.
    destruct e0.
    intros y Hy.
    destruct (eq_var x y); subst.
    exists o'; split; auto.
    inv H2; auto.
    destruct H9.
    destruct H5.
    intuition eauto.
    destruct H5.
    intuition eauto.
    destruct (H10 y).
    destruct (H1 y); intuition.
    elim n; auto.
    exists x0; destruct H3; split; auto.
    destruct H5.
    destruct (excluded_middle (fst x0 = fst o')).
    destruct H9.
    destruct H12.
    exists 1; intuition; congruence.
    destruct H12; intuition.
    exists (Datatypes.S x1); congruence.
    destruct H9.
    rewrite H9; eauto.
    apply gamma_lock_monotone with (1:=H1); auto.
    repeat intro; destruct H9.
    destruct (H10 _ H3) as [O [V1 V2]].
    exists O; split; auto.
    destruct V2 as [n V2].
    destruct (excluded_middle (fst O = fst o')).
    destruct H7.
    intuition congruence.
    destruct H7; intuition.
    rewrite H9; eauto.
    rewrite H5; eauto.

    eapply gamma_cs_acquire; eauto.
    intro; elim n; eapply HL; eauto.
    congruence.
    apply gamma_cs_monotone_cons; eauto.
    (* MonitorExit *)
    inv Hcs.
    destruct (Hp _ _ H4 H6 c) as [_ HP].
    eauto with datatypes.
    assert (HC:=HP _ _ H8).
    inv HC.
    intros z oz Hz.
    unfold upd_thread in *.
    MLcase' o z.
    inv Hz.
    constructor 2 with cl; auto.
    unfold gamma_stack in *.
    rewrite H in H7; inv H7.
    apply gamma_list_monotone with (1:=H0); auto.
    repeat intro.
    unfold gamma_stack in *.
    rewrite H in H7; inv H7.
    destruct e.
    destruct (H1 x); intuition.
    destruct e; [idtac|destruct (H1 x); intuition].
    destruct (H1 x); auto.
    destruct (H10 x); auto.
    exists x1; destruct H7; split; auto.
    inv H13.
    inv H16.
    destruct (excluded_middle (fst x1=fst o')).
    assert (x1=o') by eauto with datatypes.
    subst.
    assert (PtL c m i x (snd o')) by eauto with datatypes.
    assert (PtL c m i x0 (snd o')) by eauto with datatypes.
    elim H5; eauto.
    destruct H9.
    rewrite H9; auto.
    apply gamma_cs_monotone_cons.
    eapply gamma_cs_release; eauto.
    intro; elim n; eapply HL; eauto.
    congruence.
  Qed.

  Lemma step_correct : forall cg L sigma mu L' sigma' mu' a ls,
    MustLock cg ->
    ValidReturns ->
    (forall o cs c m i s rho o' x, L o = Some ((m, i, c, s, rho)::cs) -> 
      rho x = Loc o' -> PtL c m i x (snd o')) ->
    (forall o z, L o <> None -> fst z = fst o -> L z <> None -> o = z) ->
    (forall o cs c m i s rho, L o = Some cs -> In (m, i, c, s, rho) cs -> 
      forall x x' o o', rho x = Loc o -> rho x' = Loc o' -> fst o = fst o' -> o = o') ->
    (forall o cs c m i s rho, L o = Some cs -> In (m, i, c, s, rho) cs -> cg m c) ->
    (forall o cs c m i s rho, L' o = Some cs -> In (m, i, c, s, rho) cs -> cg m c) ->
    step p (L,sigma,mu) (L',sigma',mu') a ->
    gamma_thread mu ls L ->
    gamma_thread mu' (sigma'::ls) L'.
  Proof.
    intros cg L sigma mu L' sigma' mu' a ls Hp Hr HPT Hi Hrho Hi1 Hi2 Hs Ht.
    inv Hs.
    eapply step3_correct with (8:=H6); eauto.
    intros; eapply (Hi1 o); eauto.
    intros; eapply Hi; try congruence.
  Qed.

End MustLock.

Definition SafeCG (p:program) (cg:method->mcontext->Prop) : Prop :=
    forall sigma mu L cs l,
      reachable p (L,sigma,mu) ->
      L l =Some cs ->
      forall c m i s rho,
        In (m, i, c, s, rho) cs -> 
        cg m c.

Definition SafePtL (p:program) (PtL:mcontext->method->line->var->pcontext->Prop) : Prop :=
    forall sigma mu L cs l c m i s rho x o,
      reachable p (L,sigma,mu) ->
      L l =Some ((m, i, c, s, rho)::cs) ->
        rho x = Loc o -> PtL c m i x (snd o).

  Lemma reachable_correct : forall p cg PtL st S Locks ls,
    SafeCG p cg ->
    SafePtL p PtL ->
    MustLock p PtL S Locks cg  ->
    ValidReturns p ->
    reachable_h p ls st ->
    match st with (L,sigma,mu) =>
      gamma_thread p S Locks mu ls L
    end.
  Proof.
    induction 5.
    unfold init.
    unfold threads_init.
    intros o cs Ho.
    destruct eq_memloc'; try discriminate.
    inv Ho.
    assert (P1:=main_prop_1 p).
    assert (P2:=main_class_prop p).
    constructor 2 with (main_class p); auto.
    elim (H1 (main_class p) (main p)) with init_mcontext; auto.
    intros.
    destruct H3.
    unfold gamma_stack.
    apply gamma_list_monotone with (1:=H3).
    constructor.
    unfold SafeCG in *.
    apply H with (sigma_init p) (fun _:location => Free) (threads_init p) ((main p,0,init_mcontext,nil,fun _=> Null)::nil:call_stack) (run_address,None) 0 (nil:op_stack) (fun _:var => Null).
    generalize (reachable_0 p); unfold init; auto.
    unfold threads_init.
    destruct eq_memloc'; auto.
    intuition.
    left; auto.
    elim (H1 (main_class p) (main p)) with init_mcontext; auto.
    intros.
    destruct H3.
    repeat intro.
    assert (V:=H5 _ H6).
    elim V.
    apply H with (sigma_init p) (fun _:location => Free) (threads_init p) ((main p,0,init_mcontext,nil,fun _=> Null)::nil:call_stack) (run_address,None) 0 (nil:op_stack) (fun _:var => Null).
    generalize (reachable_0 p); unfold init; auto.
    unfold threads_init.
    destruct eq_memloc'; auto.
    intuition.
    left; auto.
    constructor.
    destruct st as [[L0 sigma0]mu0].
    eapply step_correct; eauto.
    assert (R:=I.reachable_h_reachable _ _ _ H3).
    intros; eapply H0; eauto.
    eapply I.reachable_h_L_Wf with (1:=H3).
    intros.
    assert (R:=I.reachable_wf _ _ (I.reachable_h_reachable _ _ _ H3) _ _ H5).
    inv R.
    assert (W:=I.reachable_wf_heap _ _ (I.reachable_h_reachable _ _ _ H3)); eauto.
    destruct o0; destruct o'; simpl in H9; subst.
    replace p0 with p1; auto.
    apply W with l1; eauto.
    assert (W1:=H10 _ H6).
    inv W1.
    eauto.
    assert (W1:=H10 _ H6).
    inv W1.
    eauto.
    intros.
    assert (R:=I.reachable_h_reachable _ _ _ H3).
    eapply H; eauto.
    intros.
    assert (R:=I.reachable_h_reachable _ _ _ H3).
    assert (reachable p (L,sigma,mu)).
    econstructor 2; eauto.
    eapply H; eauto.
  Qed.

  Record ml : Type := make_ML {
    locks : mcontext -> method -> line -> var -> Prop;
    s : mcontext -> method -> line -> list expr
  }.

  Definition MustLockSpec 
    (p:program)
    (PtL:mcontext->method->line->var->pcontext->Prop)
    (cg:method->mcontext->Prop) (ML:ml) : Prop :=
    MustLock p PtL ML.(locks) ML.(s) cg.

  Fixpoint is_origin' (x:var) (e:expr') : bool :=
    match e with
      | Var y => if eq_var x y then true else false
      | Field e f => is_origin' x e
    end.

  Definition is_origin (x:var) (e:expr) : bool :=
    match e with
      | Top => false
      | E e => is_origin' x e
    end.

  Lemma is_origin'_correct : forall sigma x o1 l ls e v2,
    In sigma ls -> sigma o1 <> None ->
    l x = Loc o1 ->
    gamma_expr' l ls e v2 ->
    is_origin' x e = true ->
    forall o2, v2 = Loc o2 -> heap_reach ls o1 o2.
  Proof.
    induction 4; simpl.
    destruct eq_var; intros; try discriminate.
    subst; replace o1 with o2 in * by congruence.
    econstructor 1; eauto.
    intros.
    assert (IH:=IHgamma_expr' H5 _ (refl_equal _)); clear IHgamma_expr'.
    econstructor 2; eauto.
  Qed.

  Lemma is_origin_correct : forall sigma x o1 l ls e v2,
    In sigma ls -> sigma o1 <> None ->
    l x = Loc o1 ->
    gamma_expr l ls e v2 ->
    is_origin x e = true ->
    forall o2, v2 = Loc o2 -> heap_reach ls o1 o2.
  Proof.
    destruct 4; simpl; intros.
    discriminate.
    eapply is_origin'_correct; eauto.
  Qed.

  Definition mustLock 
    (PtL:mcontext -> method -> line -> var -> (pcontext -> Prop))
    (ML:ml) (ppt:PPT) : (pcontext -> Prop) :=
    match ppt with
      (m,i,c) => match body m i with
                   | None => fun _ => False
                   | Some ins => 
                     match ins with
                       | GetField f => 
                         match ML.(s) c m i with
                           | e::_ => fun pcx =>
                             exists x, (ML.(locks) c m i) x /\
                               is_origin x e = true /\
                               forall pcx', PtL c m i x pcx' <-> pcx = pcx'
                           | _ => (fun _ => False)
                         end
                       | PutField f => 
                         match ML.(s) c m i with
                           | _::e::_ => fun pcx =>
                             exists x, (ML.(locks) c m i) x /\
                               is_origin x e = true /\
                               forall pcx', PtL c m i x pcx' <-> pcx = pcx'
                           | _ => (fun _ => False)
                         end
                       | _ => fun _ => False
                     end
                 end
    end.

  Lemma mustLock_correct : forall p cg (PtL:mcontext -> method -> line -> var -> (pcontext -> Prop)) ML
    (SP:SafePtL p PtL),
    SafeCG p cg ->
    MustLockSpec p PtL cg ML  ->
    ValidReturns p ->
    forall ls L sigma mu st' a ppt o o1 c2,
      reachable_h p ls (L,sigma,mu) ->
      step p (L,sigma,mu) st' a -> 
      (forall o c m i s rho cs, L o = Some ((m,i,c,s,rho)::cs) ->
          forall x o0, rho x = Loc o0 -> PtL c m i x (snd o0)) ->
      get_ppt ppt a ->
      get_owner o a ->
      get_target o1 a ->
      mustLock PtL ML ppt c2 ->
      exists l2, exists n ,
        mu l2 = Held (fst o) n /\
        heap_reach ls (l2,c2) o1.
  Proof.
    intros.
    destruct ML; simpl in *.
    assert (gamma_thread p locks0 s0 mu ls L).
    eapply reachable_correct with (5:=H2); eauto.
    inv H3; try (inv H5; fail).
    inv H15; try (inv H5; fail).
    inv H20; try (inv H5; fail).
    inv H17; try (inv H5; fail).
    generalize (H9 _ _ H16); clear H9; intros T.
    inv T.
    inv H6; inv H7; inv H5; inv HYP2.
  
    simpl in H8.
    rewrite HYP1 in H8.
    inv H17.
    rewrite <- H3 in *.
    destruct H8 as [x [G1 [G2 G3]]].
    destruct (H18 _ G1) as [o1 [G4 [n G5]]].
    exists (fst o1); exists n; split; auto.
    apply is_origin_correct with sigma' x rho' E0 (Loc o'); auto.
    apply I.reachable_h_In with (1:=H2); eauto.
    assert (PtL c m i x (snd o1)).
    eapply H4; eauto.
    assert (c2=snd o1) by (destruct (G3 (snd o1)); intuition).
    subst.
    destruct o1 as [l1 c1].
    simpl in *.
    destruct (I.reachable_wf _ _ (I.reachable_h_reachable _ _ _ H2) _ _ H16).
    assert (I.wf1 (m, i, c, Loc o' :: s2, rho',sigma')).
    apply H6; left; auto.
    inv H10; eauto.
    assert (PtL c m i x (snd o1)).
    eapply H4; eauto.
    assert (c2=snd o1) by (destruct (G3 (snd o1)); intuition).
    subst.
    destruct o1 as [l1 c1]; auto.
    
    simpl in H8.
    rewrite HYP1 in H8.
    inv H17.
    inv H9.
    rewrite <- H3 in *.
    destruct H8 as [x [G1 [G2 G3]]].
    destruct (H18 _ G1) as [o1 [G4 [n G5]]].
    exists (fst o1); exists n; split; auto.
    apply is_origin_correct with sigma x rho' E1 (Loc o'); auto.
    apply I.reachable_h_In with (1:=H2); eauto.
    assert (PtL c m i x (snd o1)).
    eapply H4; eauto.
    assert (c2=snd o1) by (destruct (G3 (snd o1)); intuition).
    subst.
    destruct o1 as [l1 c1].
    simpl in *.
    destruct (I.reachable_wf _ _ (I.reachable_h_reachable _ _ _ H2) _ _ H16).
    assert (I.wf1 (m, i, c,v:: Loc o' :: s', rho',sigma)).
    apply H6; left; auto.
    inv H9; eauto.
    assert (PtL c m i x (snd o1)).
    eapply H4; eauto.
    assert (c2=snd o1) by (destruct (G3 (snd o1)); intuition).
    subst.
    destruct o1 as [l1 c1]; auto.
  Qed.


End MakeMustLock.

