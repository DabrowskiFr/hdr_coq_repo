Require Export semantic.
Require Export standard_semantic.

Module S := StandardSemantic.

Section equiv.

Variable p : program.

(*
Variable pequiv : S1.C.pcontext -> S2.C.pcontext -> Prop.
Notation "x ~p y" := (pequiv x y) (at level 10).

Variable mequiv : S1.C.mcontext -> S2.C.mcontext -> Prop.
Notation "x ~m y" := (mequiv x y) (at level 10).
*)

Inductive equiv_ppt : Sem.PPT -> S.PPT -> Prop :=
| equiv_ppt_def : forall m i,
  equiv_ppt (m,i) (m,i,tt).
Notation "x ~ppt y" := (equiv_ppt x y) (at level 10).

Inductive equiv_memory_location (sigma:Sem.heap) : location -> S.memory_location -> Prop :=
  | equiv_memory_location_def : forall l c fd,
    sigma l = Some (c,fd) ->
    equiv_memory_location sigma l (l,c).
Notation "sigma '|-' x ~ml y" := (equiv_memory_location sigma x y) (at level 10).

Inductive equiv_memory_location' (sigma:Sem.heap) : location -> S.memory_location' -> Prop :=
| equiv_memory_location_def0 : 
  equiv_memory_location' sigma 1%positive (1%positive,None)
| equiv_memory_location_def1 : forall l p,
  l<>1%positive ->
  equiv_memory_location sigma l (l,p) ->
  equiv_memory_location' sigma l (l,Some p).
Notation "sigma '|-' x ~ml' y" := (equiv_memory_location' sigma x y) (at level 10).

Inductive equiv_val (sigma:Sem.heap) : Sem.val -> S.val -> Prop :=
| equiv_val_null : equiv_val sigma Sem.Null S.Null
| equiv_val_loc : forall m1 m2, 
  sigma |- m1 ~ml m2 -> equiv_val sigma (Sem.Loc m1) (S.Loc m2).
Hint Constructors equiv_val.
Notation "sigma '|-' x ~v y" := (equiv_val sigma x y) (at level 10).

Definition equiv_local (sigma:Sem.heap) (l1:Sem.local) (l2:S.local) : Prop := 
  forall x, sigma |- (l1 x) ~v (l2 x).
Notation "sigma '|-' x ~l y" := (equiv_local sigma x y) (at level 10).

Definition equiv_object (sigma:Sem.heap) (o1:field -> Sem.val) (o2:field -> S.val) : Prop := 
  forall f, sigma |- (o1 f) ~v (o2 f).
Notation "sigma '|-' x ~o y" := (equiv_object sigma x y) (at level 10).

Inductive equiv_stack (sigma:Sem.heap) : Sem.op_stack -> S.op_stack -> Prop :=
| equiv_stack_nil : equiv_stack sigma nil nil
| equiv_stack_cons : forall v1 v2 s1 s2,
  sigma |- v1 ~v v2 -> equiv_stack sigma s1 s2 -> equiv_stack sigma (v1::s1) (v2::s2).
Notation "sigma '|-' x ~s y" := (equiv_stack sigma x y) (at level 10).

Inductive equiv_bot (A1 A2:Set) (equiv:A1->A2->Prop) : option A1 -> option A2 -> Prop :=
| equiv_bot_none : equiv_bot A1 A2 equiv None None
| equiv_bot_some : forall a1 a2, equiv a1 a2 -> equiv_bot A1 A2 equiv (Some a1) (Some a2).
Implicit Arguments equiv_bot [A1 A2].

Definition equiv_heap (h1:Sem.heap) (h2:S.heap) : Prop := 
  (forall  l c fd1, h1 l = Some (c,fd1) -> exists fd2, h2 (l,c) = Some fd2 /\ h1 |- fd1 ~o fd2)
  /\
  (forall  l c fd2, h2 (l,c) = Some fd2 -> exists fd1, h1 l = Some (c,fd1) /\ h1 |- fd1 ~o fd2).
Notation "x ~h y" := (equiv_heap x y) (at level 10).

Inductive equiv_frame (sigma:Sem.heap) : Sem.frame -> S.frame -> Prop :=
| equiv_frame_def : forall m i s1 s2 rho1 rho2,
  sigma |- s1 ~s s2 -> sigma |- rho1 ~l rho2 ->
  equiv_frame sigma (m,i,s1,rho1) (m,i,tt,s2,rho2).
Notation "sigma '|-' x ~f y" := (equiv_frame sigma x y) (at level 10).

Inductive equiv_callstack (sigma:Sem.heap) : Sem.call_stack -> S.call_stack -> Prop :=
| equiv_callstack_nil : equiv_callstack sigma nil nil
| equiv_callstack_cons : forall v1 v2 s1 s2,
  sigma |- v1 ~f v2 -> equiv_callstack sigma s1 s2 -> equiv_callstack sigma (v1::s1) (v2::s2).
Notation "sigma '|-' x ~cs y" := (equiv_callstack sigma x y) (at level 10).

Definition equiv_threads (sigma:Sem.heap) (L1:Sem.threads) (L2:S.threads) : Prop := 
  (L1 1%positive <> None)
  /\
  (forall m1, L1 m1 <> None ->
    exists m2, sigma |- m1 ~ml' m2 /\ equiv_bot (equiv_callstack sigma) (L1 m1) (L2 m2))
  /\
  (forall m2, L2 m2 <> None ->
    exists m1, sigma |- m1 ~ml' m2 /\ equiv_bot (equiv_callstack sigma) (L1 m1) (L2 m2)).
Notation "sigma '|-' x ~t y" := (equiv_threads sigma x y) (at level 10).

Inductive equiv_event : Sem.event -> S.event -> Prop :=
| equiv_event_def : forall k ppt1 ppt2 f, 
  ppt1 ~ppt ppt2 -> equiv_event (k,ppt1,f) (k,ppt2,f).
Notation "x ~e y" := (equiv_event x y) (at level 10).

Inductive equiv_action (sigma:Sem.heap) : Sem.action -> S.action -> Prop :=
| equiv_action_none : equiv_action sigma None None
| equiv_action_some : forall o1 e1 o1' o2 e2 o2',
  sigma |- o1 ~ml' o2 -> 
  e1 ~e e2 ->
  sigma |- o1' ~ml o2' -> 
  equiv_action sigma (Some (o1,e1,o1')) (Some (o2,e2,o2')).
Notation "sigma '|-' x ~a y" := (equiv_action sigma x y) (at level 10).

Lemma equiv_subst : forall sigma rho1 rho2 x v1 v2,
  sigma |- v1 ~v v2 -> 
    sigma |- rho1 ~l rho2 -> 
      sigma |- (Sem.subst rho1 x v1) ~l (S.subst rho2 x v2).
Proof.
  intros.
  intros y; unfold Sem.subst, S.subst.
  comp x y; auto.
Qed.
Hint Resolve equiv_subst.

Lemma equiv_updatefield : forall sigma o1 o2 f v1 v2,
  sigma |- v1 ~v v2 -> 
    sigma |- o1 ~o o2 ->
      sigma |- (Sem.updateField o1 f v1) ~o (S.updateField o2 f v2).
Proof.
  intros.
  intros y; unfold S.updateField, Sem.updateField.
  comp f y; auto.
Qed.
Hint Resolve equiv_updatefield.

Lemma read_equiv : forall sigma1 sigma2 o1 f v1 o2,
  sigma1 ~h sigma2 -> 
  sigma1 |- o1 ~ml o2 ->
  Sem.read sigma1 o1 f v1 ->
  exists v2, S.read sigma2 o2 f v2 /\ sigma1 |- v1 ~v v2.
Proof.
  intros sigma1 sigma2 o1 f v1 o2 H H0 H1.
  destruct H1 as [o [H1 H2]].
  destruct H as [H H'].
  destruct o as [c fd]; simpl in *.
  elim H with (1:=H1);clear H; intros fd2 [T1 T2].
  exists (fd2 f); split.
  exists fd2; split; auto.
  inv H0; congruence.
  subst; auto.
Qed.

Lemma read_equiv' : forall sigma1 sigma2 o1 f v2 o2,
  sigma1 ~h sigma2 -> 
  sigma1 |- o1 ~ml o2 ->
  S.read sigma2 o2 f v2 ->
  exists v1, Sem.read sigma1 o1 f v1 /\ sigma1 |- v1 ~v v2.
Proof.
  intros sigma1 sigma2 o1 f v2 o2 H H0 H1.
  destruct H1 as [o [H1 H2]].
  destruct H as [H H'].
  destruct o2 as [l c]; simpl in *.
  elim H' with (1:=H1);clear H; intros fd1 [T1 T2].
  exists (fd1 f); split.
  exists (c,fd1); split; auto.
  inv H0; congruence.
  subst; auto.
Qed.

Ltac MLcase2 x y := destruct (S.eq_memloc x y); [subst|idtac].
Ltac MLcase1 x y := destruct (Sem.eq_memloc x y); [subst|idtac].
Ltac MLcase2' x y := destruct (S.eq_memloc' x y); [subst|idtac].

Lemma write_monotone_ml : forall sigma o f v sigma',
  Sem.write sigma o f v sigma' ->
  forall ml1 ml2, sigma |- ml1 ~ml ml2 -> sigma' |- ml1 ~ml ml2.
Proof.
  intros.
  destruct H.
  destruct H as [m [T1 T2]].
  inv H0.
  MLcase1 o ml1.
  rewrite T1 in H; inv H.
  simpl in *.
  econstructor; eauto.
  econstructor; eauto.
  rewrite H1; eauto.
Qed.
Implicit Arguments write_monotone_ml.

Lemma write_monotone_v : forall sigma o f v sigma',
  Sem.write sigma o f v sigma' ->
  forall v1 v2, sigma |- v1 ~v v2 -> sigma' |- v1 ~v v2.
Proof.
  intros.
  assert (M:=write_monotone_ml H).
  destruct H.
  destruct H as [m [T1 T2]].
  inv H0; constructor; eauto.
Qed.
Implicit Arguments write_monotone_v.

Lemma write_equiv : forall sigma1 sigma2 o1 f v1 v2 o2 sigma1',
  sigma1 ~h sigma2 -> 
  sigma1 |- o1 ~ml o2 -> 
  sigma1 |- v1 ~v v2 ->
  Sem.write sigma1 o1 f v1 sigma1' ->
  exists sigma2', 
    S.write sigma2 o2 f v2 sigma2' /\ sigma1' ~h sigma2'.
Proof.
  intros sigma1 sigma2 o1 f v1 v2 o2 sigma1' H H0 H1 H2.
  assert (M:=write_monotone_v H2).
  destruct H2.
  destruct H2 as [[c fd] [H2 H4]].
  inv H0; simpl in *.
  rewrite H5 in H2; inv H2.
  destruct H as [T1 T2].
  elim T1 with (1:=H5); intros fd2 [W1 W2].
  exists (fun o => if S.eq_memloc o (o1,c) then Some (S.updateField fd2 f v2) else sigma2 o); 
    split.
  split; intros.
  exists fd2; split; auto.
  destruct S.eq_memloc; intuition.
  destruct S.eq_memloc; congruence.
  split; intros.
  destruct S.eq_memloc.
  inv e.
  repeat (econstructor; eauto).
  repeat intro.
  unfold S.updateField.
  rewrite H in H4; inv H4.
  unfold Sem.updateField.
  destruct eq_pos; subst; auto.
  destruct (eq_pos l o1); subst.
  try congruence.
  rewrite H3 in H; try congruence.  
  elim T1 with (1:=H); intros fd3 [V1 V2].
  exists fd3; split; auto.
  unfold equiv_object in *; eauto.
  destruct S.eq_memloc.
  inv e; inv H.
  exists (Sem.updateField fd f v1); split; auto.
  apply equiv_updatefield; eauto.
  unfold equiv_object in *; eauto.
  destruct (eq_pos l o1); subst.
  elim T2 with (1:=H); intros fd3 [V1 V2].
  rewrite V1 in H5; inv H5; intuition.
  rewrite H3; auto.
  elim T2 with (1:=H); intros fd3 [V1 V2].
  unfold equiv_object in *; eauto.
Qed.

Lemma write_equiv' : forall sigma1 sigma2 o1 f v1 v2 o2 sigma2',
  sigma1 ~h sigma2 -> 
  sigma1 |- o1 ~ml o2 -> 
  sigma1 |- v1 ~v v2 ->
  S.write sigma2 o2 f v2 sigma2'  ->
  exists sigma1', 
    Sem.write sigma1 o1 f v1 sigma1' /\ sigma1' ~h sigma2'.
Proof.
  intros sigma1 sigma2 o1 f v1 v2 o2 sigma2' H H0 H1 H2.
  destruct H2.
  destruct H2 as [fd [H2 H4]].
  inv H0; simpl in *.
  destruct H as [T1 T2].
  elim T2 with (1:=H2); intros fd2 [W1 W2].
  rewrite H5 in W1; inv W1.
  assert (W:Sem.write sigma1 o1 f v1
     (fun o : location =>
      if Sem.eq_memloc o o1
      then Some (c, Sem.updateField fd2 f v1)
      else sigma1 o)).
  split; intros.
  exists (c,fd2); split; auto.
  destruct Sem.eq_memloc; intuition.
  destruct Sem.eq_memloc; congruence.
    exists ((fun o => if Sem.eq_memloc o o1 then Some (c,Sem.updateField fd2 f v1) else sigma1 o):Sem.heap); 
    split; auto.
  assert (M:=write_monotone_v W).
  split; intros.
  destruct (Sem.eq_memloc l o1).
  inv e; inv H.
  repeat (econstructor; eauto).
  repeat intro; apply M; auto.
  apply equiv_updatefield; eauto.
  rewrite H3; try congruence.
  elim T1 with (1:=H); intros fd3 [V1 V2].
  exists fd3; split; auto.
  unfold equiv_object in *; eauto.
  destruct (Sem.eq_memloc l o1); subst.
  destruct (excluded_middle (c=(c0:Standard.pcontext))); subst.
  repeat (econstructor; eauto).  
  intro; apply M; auto.
  replace fd0 with (StandardSemantic.updateField fd f v2).
  apply equiv_updatefield; auto.
  unfold Standard.pcontext, classId in *; congruence.
  rewrite H3 in H; try congruence.
  elim T2 with (1:=H); intros fd3 [V1 V2].
  elim H0; congruence.
  rewrite H3 in H; try congruence.
  elim T2 with (1:=H); intros fd3 [V1 V2].
  repeat (econstructor; eauto).
  intro; apply M; auto.
Qed.

Lemma alloc_monotone_ml : forall sigma o cid sigma',
  Sem.alloc sigma cid o sigma' ->
  forall ml1 ml2, sigma |- ml1 ~ml ml2 -> sigma' |- ml1 ~ml ml2.
Proof.
  intros.
  destruct H as [T [T1 T2]].
  inv H0.
  MLcase1 o ml1.
  congruence.
  econstructor.
  rewrite T2; eauto.
Qed.
Implicit Arguments alloc_monotone_ml.

Lemma alloc_monotone_v : forall sigma o cid sigma',
  Sem.alloc sigma cid o sigma' ->
  forall v1 v2, sigma |- v1 ~v v2 -> sigma' |- v1 ~v v2.
Proof.
  intros.
  elim H; intros T [T1 T2].
  inv H0; constructor.
  eapply alloc_monotone_ml; eauto.
Qed.
Implicit Arguments alloc_monotone_v.

Lemma alloc_equiv : forall sigma1 sigma2 o1 sigma1' cid,
  sigma1 ~h sigma2 -> 
  Sem.alloc sigma1 cid o1 sigma1' ->
  sigma1' |- o1 ~ml (o1,cid) -> 
  exists sigma2',
    S.alloc sigma2 (o1,cid) sigma2' /\ sigma1' ~h sigma2'.
Proof.
  intros sigma1 sigma2 o1 sigma1' cid H H0.
  generalize H0; intros A.
  destruct H0 as [H1 [H2 H3]].
  exists (fun o => if S.eq_memloc o (o1,cid) then Some (fun _ => S.Null) else sigma2 o).
  repeat split; auto.

  destruct H as [T1 T2].
  case_eq (sigma2 (o1,cid)); intros; auto.
  elim T2 with (1:=H); intuition; congruence.

  destruct S.eq_memloc; intuition.

  intros.
  destruct S.eq_memloc; subst; intuition.
  
  intros.
  destruct H as [T1 T2].
  destruct S.eq_memloc; subst.
  inv e.
  rewrite H2 in H4; inv H4.
  repeat (econstructor; eauto).
  destruct (eq_pos l o1); subst.
  elim n; inv H0; congruence.
  rewrite H3 in H4; try congruence.
  elim T1 with (1:=H4); intros fd [B1 B2].
  repeat (econstructor; eauto).
  intro; eapply alloc_monotone_v; eauto.

  intros.
  destruct (S.eq_memloc (l,c) (o1,cid)).
  inv e; inv H4.
  inv H0.
  repeat (econstructor; eauto).
  rewrite H6 in H2; inv H2.
  intros; constructor.
  destruct (eq_pos l o1); subst.
  destruct H as [_ H].
  elim H with (1:=H4); intros fd1 [F1 F2].
  congruence.
  rewrite H3; try congruence.
  destruct H as [_ H].
  elim H with (1:=H4); intros fd1 [F1 F2].
  repeat (econstructor; eauto).
  intro; eapply alloc_monotone_v; eauto.
Qed.

Lemma equiv_upd_thread : forall L1 L2 o1 o2 cs1 cs2 sigma,
  sigma |- L1 ~t L2 ->
  sigma |- o1 ~ml' o2 -> 
  sigma |- cs1 ~cs cs2 ->
  sigma |- (Sem.upd_thread L1 o1 cs1) ~t (S.upd_thread L2 o2 cs2).
Proof.
  intros L1 L2 o1 o2 cs1 cs2 sigma H H0 H1.
  unfold Sem.upd_thread, S.upd_thread; split; [idtac|split]; intros.
  destruct H as [H _ ].
  destruct (Sem.eq_memloc o1 1%positive); subst; congruence.
  destruct Sem.eq_memloc; subst.
  repeat (econstructor; eauto).
  destruct S.eq_memloc'; subst.
  constructor; auto.
  intuition.
  destruct H as [ _ [H _]].
  elim H with (1:=H2); intros m2 [M1 M2].
  repeat (econstructor; eauto).
  destruct S.eq_memloc'; subst.
  elim n; inv M1; inv H0; congruence.
  auto.

  destruct S.eq_memloc'; subst.
  repeat (econstructor; eauto).
  destruct Sem.eq_memloc; subst.
  constructor; auto.
  intuition.
  destruct H as [_[_ H]].
  elim H with (1:=H2); intros m1 [M1 M2].
  repeat (econstructor; eauto).
  destruct Sem.eq_memloc; subst.
  elim n; inv M1; inv H0; try congruence.
  inv H6; inv H4; try congruence.
  auto.
Qed.

Lemma s_monotone : forall sigma1 sigma1' s1 s2,
  sigma1 |- s1 ~s s2 ->
  (forall m1 m2, sigma1 |- m1 ~ml m2 -> sigma1' |- m1 ~ml m2) ->
  (forall v1 v2, sigma1 |- v1 ~v v2 -> sigma1' |- v1 ~v v2) ->
  sigma1' |- s1 ~s s2.
Proof.
  induction 1; intros; constructor; eauto.
Qed.

Lemma cs_monotone : forall sigma1 sigma1' cs1 cs2,
  sigma1 |- cs1 ~cs cs2 ->
  (forall m1 m2, sigma1 |- m1 ~ml m2 -> sigma1' |- m1 ~ml m2) ->
  (forall v1 v2, sigma1 |- v1 ~v v2 -> sigma1' |- v1 ~v v2) ->
  sigma1' |- cs1 ~cs cs2.
Proof.
  induction 1; intros; constructor; eauto.
  inv H; constructor; eauto.
  eapply s_monotone; eauto.
  intro; eauto.
Qed.

Lemma L_monotone : forall sigma1 sigma1' L1 L2,
  sigma1 |- L1 ~t L2 ->
  (forall m1 m2, sigma1 |- m1 ~ml m2 -> sigma1' |- m1 ~ml m2) ->
  (forall v1 v2, sigma1 |- v1 ~v v2 -> sigma1' |- v1 ~v v2) ->
  sigma1' |- L1 ~t L2.
Proof.
  intros.
  destruct H as [V [V1 V2]]; split; [idtac;clear V1 V2|split; clear V;[clear V2|clear V1]]; intros.
  auto.  
  elim V1 with (1:=H); clear V1; intros m2 [M1 M2].
  exists m2; split; eauto.
  inv M1; constructor; eauto.
  inv M2; constructor.
  eapply cs_monotone; eauto.
  elim V2 with (1:=H); clear V2; intros m1 [M1 M2].
  exists m1; split; eauto.
  inv M1; constructor; eauto.
  inv M2; constructor.
  eapply cs_monotone; eauto.
Qed.

Lemma equiv_app : forall sigma s1_1 s1_2 s2,
  sigma |- (s1_1++s1_2) ~s s2 -> 
  exists s2_1, exists s2_2, s2 = s2_1++s2_2 /\ sigma |- s1_1 ~s s2_1 /\ sigma |- s1_2 ~s s2_2 /\
    length s1_1 = length s2_1.
Proof.
  induction s1_1; simpl; intros.
  exists nil; exists s2; repeat split; auto.
  constructor.
  inv H.
  elim IHs1_1 with (1:=H4); auto.
  intros s2_1 [s2_2 [T1 [T2 [T3 T4]]]].
  exists (v2::s2_1); exists s2_2; repeat split; auto.
  rewrite T1; auto.
  constructor; auto.
  simpl; congruence.
Qed.

Lemma equiv_stack_nth : forall sigma s1 s2,
  sigma |- s1 ~s s2 -> 
  forall x, sigma |- (nth x s1 Sem.Null) ~v (nth x s2 S.Null).
Proof.
  induction 1; destruct x; simpl; auto.
Qed.

Lemma step_equiv : forall sigma1 sigma2 sigma1' mu mu' L1 L2 L1' a1,
  sigma1 |- L1 ~t L2 -> 
  sigma1 ~h sigma2 -> 
  Sem.step p (L1,sigma1,mu) (L1',sigma1',mu') a1 ->
  exists a2, exists L2', exists sigma2', 
    S.step p (L2,sigma2,mu) (L2',sigma2',mu') a2 /\
    sigma1' |- L1' ~t L2' /\ 
    sigma1' |- a1 ~a a2 /\ 
    sigma1' ~h sigma2'.
Proof.
  intros sigma1 sigma2 sigma1' mu mu' L1 L2 L1' a1 H H0 H1.
  inv H1.
  elim H; intros _ [HL _].
  elim HL with o; try congruence; clear HL; intros m2 [M1 M2].
  rewrite H10 in M2; inv M2.
  inv H3.
  
  inv H9.
  inv H15.
  inv H5.
  inv H12.

  exists None; 
    exists (S.upd_thread L2 m2 ((m, S.next_line i,tt, S.Null :: s0, rho2) :: s2));
      exists sigma2; split; [idtac|split;[idtac|split]]; 
        try (auto;fail); try (constructor; fail).
  repeat (econstructor; eauto).
  eapply equiv_upd_thread; eauto; repeat (econstructor; eauto).

  exists None; 
    exists (S.upd_thread L2 m2 ((m, S.next_line i,tt, rho2 x :: s0, rho2) :: s2));
      exists sigma2; split; [idtac|split;[idtac|split]]; 
        try (auto;fail); try (constructor; fail).
  repeat (econstructor; eauto).
  eapply equiv_upd_thread; eauto; repeat (econstructor; eauto).

  inv H9.
  exists None; 
    exists (S.upd_thread L2 m2 ((m, S.next_line i,tt, s3, S.subst rho2 x v2) :: s2));
      exists sigma2; split; [idtac|split;[idtac|split]]; 
        try (auto;fail); try (constructor; fail).
  repeat (econstructor; eauto).
  eapply equiv_upd_thread; eauto; repeat (econstructor; eauto).

  inv H9.
  inv H4.
  elim read_equiv with (1:=H0) (2:=H3) (3:=HYP2); intros v2 [V1 V2].
  exists (Some (m2,(Get,(m,i,tt),f),m0)); 
    exists (S.upd_thread L2 m2 ((m, S.next_line i,tt, v2 :: s4, rho2) :: s2));
      exists sigma2; split; [idtac|split;[idtac|split]]; 
        try (auto;fail); try (constructor; fail).
  repeat (econstructor; eauto).
  eapply equiv_upd_thread; eauto; repeat (econstructor; eauto).
  repeat (econstructor; eauto).

  inv H9.
  inv H6.
  inv H5.
  elim write_equiv with (1:=H0) (2:=H3) (3:=H4) (4:=HYP2); intros sigma2' [V1 V2].
  exists (Some (m2,(Put,(m,i,tt),f),m0)); 
    exists (S.upd_thread L2 m2 ((m, S.next_line i,tt, s0, rho2) :: s2));
      exists sigma2'; split; [idtac|split;[idtac|split]]; 
        try (auto;fail); try (constructor; fail).
  repeat (econstructor; eauto).
  assert (W1:=write_monotone_ml HYP2).
  assert (W2:=write_monotone_v HYP2).
  eapply equiv_upd_thread; eauto.
  eapply L_monotone; eauto.
  inv M1; constructor; eauto.
  repeat (econstructor; eauto).
  eapply s_monotone; eauto.
  intro; eauto.
  eapply cs_monotone; eauto.
  assert (W1:=write_monotone_ml HYP2).
  repeat (econstructor; eauto).
  inv M1; constructor; eauto.
  
  exists None; 
    exists (S.upd_thread L2 m2 ((m, i',tt, s0, rho2) :: s2));
      exists sigma2; split; [idtac|split;[idtac|split]]; 
        try (auto;fail); try (constructor; fail).
  repeat (econstructor; eauto).
  eapply equiv_upd_thread; eauto; repeat (econstructor; eauto).

  exists None; 
    exists (S.upd_thread L2 m2 ((m, S.next_line i,tt, s0, rho2) :: s2));
      exists sigma2; split; [idtac|split;[idtac|split]]; 
        try (auto;fail); try (constructor; fail).
  repeat (econstructor; eauto).
  eapply equiv_upd_thread; eauto; repeat (econstructor; eauto).

  exists None; 
    exists (S.upd_thread L2 m2 ((m, i',tt, s0, rho2) :: s2));
      exists sigma2; split; [idtac|split;[idtac|split]]; 
        try (auto;fail); try (constructor; fail).
  repeat (econstructor; eauto).
  eapply equiv_upd_thread; eauto; repeat (econstructor; eauto).

  elim alloc_equiv with (1:=H0) (2:=HYP5).
  intros sigma2' [S1 [S2 S3]].
  exists None; 
    exists (S.upd_thread L2 m2 ((m, S.next_line i,tt, S.Loc (a,cid)::s0, rho2) :: s2));
      exists sigma2'; split; [idtac|split;[idtac|split]]; 
        try (auto;fail); try (constructor; fail).
  do 3 (econstructor; eauto).
  econstructor 2; eauto.
  repeat intro.
  inv HYP5.
  case_eq (sigma2 (a,c)); intros; auto.
  destruct H0 as [_ H0].
  elim H0 with (1:=H4); intros fd [F1 F2]; congruence.
  assert (W1:=alloc_monotone_ml HYP5).
  assert (W2:=alloc_monotone_v HYP5).
  eapply equiv_upd_thread; eauto.
  eapply L_monotone; eauto.
  inv M1; constructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  constructor; econstructor; eauto.
  destruct HYP5 as [_ [H5 _]]; eauto.
  eapply s_monotone; eauto.
  intro; eauto.
  eapply cs_monotone; eauto.
  split; auto.
  assert (W1:=alloc_monotone_ml HYP5).
  repeat (econstructor; eauto).
  destruct HYP5 as [_ [H5 _]]; eauto.

  inv H5.
  elim equiv_app with (1:=H12); intros s3 [s4 [S1 [S2 [S3 S4]]]].
  inv S3.
  inv H4.
  set (rho2':=fun x =>
        if eq_var x 0 then S.Loc m3
          else if le_gt_dec x (length args) then nth (length args - x) s3 S.Null
            else S.Null).
  exists None; 
    exists (S.upd_thread L2 m2 ((m1, 0,tt, nil, rho2')::(m, S i,tt, s5, rho2) :: s2));
      exists sigma2; split; [idtac|split;[idtac|split]]; 
        try (auto;fail); try (constructor; fail).
  econstructor; eauto.
  econstructor; eauto.
  econstructor 2; eauto.
  inv H3.
  compute.
  congruence.
  unfold rho2'; destruct eq_var; intuition.
  intros.
  unfold rho2'.
  destruct (eq_var x 0).
  apply False_ind; omega.
  destruct (le_gt_dec x (length args)); auto.
  apply False_ind; omega.
  intros.
  unfold rho2'.
  destruct (eq_var x 0).
  apply False_ind; omega.
  destruct (le_gt_dec x (length args)); auto.
  apply False_ind; omega.
  congruence.  
  eapply equiv_upd_thread; eauto; repeat (econstructor; eauto).
  intros x.
  unfold rho2'; destruct (eq_var x 0).
  subst; rewrite H14; constructor; auto.
  destruct (le_gt_dec x (length args)).
  rewrite H17; try omega.
  apply equiv_stack_nth; auto.
  unfold var in *; omega.
  rewrite H18.
  constructor.
  unfold var in *; omega.

  inv H5.
  exists None; 
    exists (S.upd_thread L2 m2 s2);
      exists sigma2; split; [idtac|split;[idtac|split]]; 
        try (auto;fail); try (constructor; fail).
  econstructor; eauto.
  econstructor; eauto.
  econstructor 3; eauto.
  eapply equiv_upd_thread; eauto; repeat (econstructor; eauto).

  inv H5.
  inv H9.
  inv H7.
  inv H5.
  exists None; 
    exists (S.upd_thread L2 m2 ((m', i', tt, v2::s2, rho0)::s0));
      exists sigma2; split; [idtac|split;[idtac|split]]; 
        try (auto;fail); try (constructor; fail).
  econstructor; eauto.
  econstructor; eauto.
  econstructor 4; eauto.
  eapply equiv_upd_thread; eauto; repeat (econstructor; eauto).

  inv H5.
  inv H9.
  inv H4.
  set (rho2':=fun x => if eq_var x 0 then S.Loc m3 else S.Null).
  exists None; 
    exists (S.upd_thread 
             (S.upd_thread L2 m2 ((m, S i, tt, s3, rho2)::s2))             
             (fst m3, Some (snd m3)) ((m1, 0, tt, nil, rho2')::nil));
      exists sigma2; split; [idtac|split;[idtac|split]]; 
        try (auto;fail); try (constructor; fail).
  econstructor; eauto.
  econstructor 2; eauto.
  inv H3; compute; congruence.
  unfold rho2'; destruct eq_var; intuition.
  intros;  unfold rho2'; destruct (eq_var (S x) 0); auto.
  inv e.
  intros; inv H3.
  rewrite H1 in H17; inv H17; simpl in *.
  case_eq (L2 (o',c)); intros; auto.
  destruct H as [_ [_ H]].
  elim H with (o',c); try congruence; intros m4 [T1 T2]; clear H.
  rewrite H3 in T2; inv T2.
  assert (m4=o').
  inv T1; try congruence.
  congruence.
  eapply equiv_upd_thread; eauto.
  eapply equiv_upd_thread; eauto; repeat (econstructor; eauto).
  destruct m3; simpl.
  inv H3.
  econstructor; eauto.
  destruct H; congruence.
  econstructor; eauto.
  repeat (econstructor; eauto).  
  intros x; unfold rho2'.
  destruct (eq_var x 0).
  subst; rewrite H19; constructor; auto.
  destruct x.
  intuition.
  rewrite H20; auto.

  inv H5.
  inv H9.
  inv H4.
  exists None; 
    exists (S.upd_thread L2 m2 ((m, S i,tt, s3, rho2) :: s2));
      exists sigma2; split; [idtac|split;[idtac|split]]; 
        try (auto;fail); try (constructor; fail).
  econstructor; eauto.
  econstructor 3; eauto.
  inv M1; inv H3; auto.
  eapply equiv_upd_thread; eauto; repeat (econstructor; eauto).

  inv H5.
  inv H9.
  inv H4.
  exists None; 
    exists (S.upd_thread L2 m2 ((m, S i,tt, s3, rho2) :: s2));
      exists sigma2; split; [idtac|split;[idtac|split]]; 
        try (auto;fail); try (constructor; fail).
  econstructor; eauto.
  econstructor 4; eauto.
  inv M1; inv H3; auto.
  eapply equiv_upd_thread; eauto; repeat (econstructor; eauto).
Qed.


Lemma init_equiv : 
  match Sem.init p, S.init p with
    | (L1,sigma1,mu1), (L2,sigma2,mu2) =>
      sigma1 |- L1 ~t L2 /\ sigma1 ~h sigma2 /\ mu1=mu2
  end.
Proof.
  intros; unfold S.init, Sem.init.
  repeat split; auto; intros.
  unfold Sem.threads_init in *.
  destruct Sem.eq_memloc; try congruence.
  elim n; compute; auto.
  unfold Sem.threads_init in *.
  destruct Sem.eq_memloc; simpl.
  exists (S.run_address, None); subst.
  split.
  constructor.
  unfold S.threads_init.
  destruct S.eq_memloc'; simpl.
  repeat constructor.
  intuition.
  intuition.
  unfold S.threads_init, Sem.threads_init in *.
  destruct S.eq_memloc'; simpl; auto.
  inv e.
  exists 1%positive.
  repeat split; auto.
  constructor.
  destruct Sem.eq_memloc; simpl; intros.
  repeat constructor.
  elim n; reflexivity.
  intuition.
  unfold Sem.sigma_init, S.sigma_init in *.  
  destruct Sem.eq_memloc; simpl; intuition.
  inv H.
  exists (fun _ => S.Null); split.
  destruct S.eq_memloc; simpl in *; auto.
  elim n.
  unfold S.init_p.
  rewrite main_prop_4.
  reflexivity.
  intro; constructor.
  congruence.
  unfold Sem.sigma_init, S.sigma_init in *.  
  destruct S.eq_memloc; simpl; intuition.
  inv H; inv e.
  exists (fun _ => Sem.Null); split.
  destruct Sem.eq_memloc; simpl in *; auto.
  elim n; reflexivity.
  intro; constructor.
  congruence.
Qed.

Lemma reach_equiv : 
  forall st, 
    Sem.reachable p st ->
    match st with (L1,sigma1,mu) =>
      exists L2, exists sigma2, 
        S.reachable p (L2,sigma2,mu) /\ sigma1 |- L1 ~t L2 /\ sigma1 ~h sigma2
    end.
Proof.
  intros until st.
  induction 1.
  generalize (S.reachable_0 p).
  case_eq (S.init p); intros [L2 sigma2] mu2.
  unfold Sem.init.
  intros.
  replace ((fun _:location => Free):S.lock) with mu2 in *.
  exists L2; exists sigma2; split; auto.
  generalize init_equiv.
  rewrite H; unfold Sem.init.
  intuition.
  unfold S.init in *.
  congruence.
  destruct st as [[L sigma]mu].
  destruct IHreachable as [L2 [sigma2 [B [B1 B2]]]].
  destruct st' as [[L' sigma']mu'].
  elim step_equiv with (L2:=L2) (sigma2:=sigma2) (3:=H'); auto.
  intros a2 [L2' [sigma2' T]].
  decompose [and] T.
  exists L2'; exists sigma2'; split; intuition.
  constructor 2 with (L2,sigma2,mu) a2; auto.
Qed.

Lemma concurrent_access_same_class : forall st L1 L2 sigma1 sigma2 mu1 mu2 o1 o2 e1 e2 o', 
  Sem.step p st (L1, sigma1, mu1) (Some (o1, e1, o')) ->
  Sem.step p st (L2, sigma2, mu2) (Some (o2, e2, o')) ->
  forall c1 fd1 c2 fd2,
    sigma1 o' = Some (c1,fd1) ->
    sigma2 o' = Some (c2,fd2) ->
    c1=c2.
Proof.
  intros.
  inv H; inv H0.
  inv H8; inv H11.
  inv H13; inv H14.
  inv H10; inv H8; try congruence.
  destruct HYP4 as [[m1 [M1 M2]] M3].
  rewrite M1 in H1; inv H1; simpl in *.
  congruence.
  destruct HYP3 as [[m1 [M1 M2]] M3].
  rewrite M1 in H2; inv H2; simpl in *.
  congruence.
  destruct HYP3 as [[m1 [M1 M2]] M3].
  rewrite M2 in H1; inv H1; simpl in *.
  destruct HYP4 as [[m2 [N1 N2]] N3].
  rewrite N2 in H2; inv H2; simpl in *.
  congruence.
Qed.

Lemma race_equiv : forall ppt ppt',
  Sem.race p ppt ppt' -> S.race_without_context p ppt ppt'.
Proof.
  intros.
  inv H.
  destruct st as [[L1 sigma1]mu].
  destruct (reach_equiv _ H0) as [L2 [sigma2 [T1 [T2 T3]]]].
  destruct st1 as [[L1' sigma1']mu'].
  elim step_equiv with (L2:=L2) (sigma2:=sigma2) (3:=H1); auto.
  intros a2' [L2' [sigma2' T]].
  decompose [and] T; clear T.
  destruct st2 as [[L1'' sigma1'']mu''].
  elim step_equiv with (L2:=L2) (sigma2:=sigma2) (3:=H2); auto.
  intros a2'' [L2'' [sigma2'' T']].
  decompose [and] T'; clear T'.
  econstructor 1 with (c1:=tt) (c2:=tt) (a1:=a2') (a2:=a2''); eauto.
  inv H6; inv H3.
  inv H14.
  inv H18; constructor.
  inv H10; inv H4.
  inv H14.
  inv H18; constructor.
  inv H6; inv H10; inv H5.
  inv H14; inv H16.
  replace o2'0 with o2'.
  constructor; auto.
  intro; subst; elim H19; inv H12; inv H6; try congruence.
  
  inv H15; inv H17.
  assert (c0=c).
  apply concurrent_access_same_class with (1:=H2) (2:=H1) (3:=H10) (4:=H5).
  congruence.
Qed.

End equiv.
