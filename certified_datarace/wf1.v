Require Export domain_prop.
Require Export List.

Module WF1 (Import S:COUNTING_SEMANTIC). 

Module Import DP := DomainProp S. 

Lemma step0_dom_eq :
  forall o ppt instr i j s s' rho rho' sigma sigma' e,
    step0 o ppt instr (i,s,rho,sigma) (j,s',rho',sigma') e ->
    (forall o, inDom o sigma' -> inDom o sigma).
Proof.
unfold inDom.
intros.
inv H; try assumption.
inv HYP2.
destruct H as [m [Ha Hb]].
destruct (excluded_middle (o2=o0)).
subst.
rewrite Ha.
discriminate.
rewrite <- (H1 o0 H).
assumption.
Qed.

(******** invariant *********)

Definition wf_heap1 (sigma:heap) : Prop :=
  forall a p1 p2, 
    inDom (a,p1) sigma ->
    inDom (a,p2) sigma -> p1=p2.

Lemma step0_wf_heap1 : forall o ppt ins i s rho sigma i' s' rho' sigma' a,
  step0 o ppt ins (i,s,rho,sigma) (i',s',rho',sigma') a ->
  wf_heap1 sigma -> wf_heap1 sigma'.
Proof.
  intros.
  inv H; try assumption.
  (* putfield *)
  unfold wf_heap1, inDom in *; inv HYP2.
  repeat intro.
  destruct H as [m [H HH]].
  destruct (excluded_middle (o1=(a,p1))); [subst|idtac].
  destruct (excluded_middle (p1=p2)); [auto|idtac].
  rewrite H1 in H3; try congruence.
  eapply H0; eauto.
  congruence.
  rewrite H1 in H2; try congruence.
  destruct (excluded_middle (o1=(a,p2))); [subst|idtac].
  eapply H0; eauto.
  congruence.
  rewrite H1 in H3; try congruence.
  apply H0 with a; auto.
Qed.

Lemma step1_wf_heap1 : forall o fr sigma fr' sigma' a,
  step1 o (fr,sigma) (fr',sigma') a ->
  wf_heap1 sigma -> wf_heap1 sigma'.
Proof.
  intros.
  inv H.
  (* step0 *)
  apply step0_wf_heap1 with (1:=HYP2); auto.
  (* new *)
  inv HYP5.
  destruct H1.
  unfold wf_heap1, inDom in *; intros.
  destruct (excluded_middle ((a0, CP m i c om pi)=(a,p1))).
  destruct (excluded_middle ((a0, CP m i c om pi)=(a,p2))).
  congruence.
  rewrite H2 in H4; try congruence.
  elim HYP2 with p2; try congruence.
  destruct (excluded_middle ((a0, CP m i c om pi)=(a,p2))).
  rewrite H2 in H3; try congruence.
  elim HYP2 with p1; try congruence.
  rewrite H2 in H3; try congruence.
  rewrite H2 in H4; try congruence.
  eapply H0; eauto.
Qed.

Lemma step2_wf_heap1 : forall p o cs sigma omg cs' sigma' omg' a,
  step2 p o (cs,sigma,omg) (cs',sigma',omg') a ->
  wf_heap1 sigma -> wf_heap1 sigma'.
Proof.
  intros.
  inv H; try assumption.
  (* step1 *)
  apply step1_wf_heap1 with (1:=H9); auto.
Qed.


Lemma step3_wf_heap1 : forall p L o cs sigma mu omg L' sigma' mu' omg' a,
  step3 p L (o,cs,sigma,mu,omg) (L',sigma',mu',omg') a ->
  wf_heap1 sigma -> wf_heap1 sigma'.
Proof.
  intros.
  inv H; try assumption.
  (* step2 *)
  apply step2_wf_heap1 with (1:=H12); auto.
Qed.

Lemma eq_memloc : forall l l':memory_location, l=l' \/ l<>l'.
Proof.
  intros; apply excluded_middle.
Qed.

Ltac MLtac l l' :=
    destruct (S.eq_memloc l l'); [subst | idtac].
Ltac MLtac' l l' :=
    destruct (S.eq_memloc' l l'); [subst | idtac].

Ltac Case' :=
  match goal with
    [ _ : context f [eq_memloc' ?x ?y] |- _ ] => 
    MLtac' x y
end.

(* Loops *)
(**********************************************************)

Definition local_coherency (p:program) (l:memory_location) 
  (cp:code_pointer) : Prop :=
  match l with (a,CP m0 i0 c0 om0 pi0) =>
    match cp with (CP m i c om pi) => 
      m=m0 -> c=c0 -> om m0 c0 = om0 m0 c0 -> 
      pi0 m0 c0 (p.(loop) (m0,i0)) <= pi m0 c0 (p.(loop) (m0,i0))
    end
  end.

Definition strong_local_coherency (p:program) (l:memory_location) 
  (cp:code_pointer) : Prop :=
  match l with (a,CP m0 i0 c0 om0 pi0) =>
    match cp with (CP m i c om pi) => 
      m=m0 -> c=c0 -> om m0 c0 = om0 m0 c0 ->
      pi0 m0 c0 (p.(loop) (m0,i0)) = pi m0 c0 (p.(loop) (m0,i0)) ->
      i0<>i /\
      (forall path, leads_to i i0 path m0 -> 
        exists k, exists ik, exists jk, 
          nth_error path k=value ik  /\ nth_error path (S k) = value jk /\ ((ik,jk) = p.(loop) (m0,i0)))
    end
  end.

Definition frame_coherency (fr:frame) (omg:mVect) :=
  match fr with (cp,s,rho) => 
    cp.(cp_om) cp.(cp_m) cp.(cp_c) <= omg cp.(cp_m) cp.(cp_c) end.

Definition global_coherency (l:memory_location) (omg:mVect) : Prop :=
  match l with (a,CP m i c om pi) =>
    om m c <= omg m c
  end.
Definition heap_global_coherency (sigma:heap) (omg:mVect) : Prop :=
  forall a m i c om pi sigma,
  inDom (a,CP m i c om pi) sigma -> 
  om m c <= omg m c.

Definition wf_frame (p:program) (fr:frame) (sigma:heap) (omg:mVect) :Prop:=
  match fr with (CP m i c om pi,s,rho) =>
    om m c <= omg m c /\
    (forall a m0 i0 c0 om0 pi0,
      inDom (a,CP m0 i0 c0 om0 pi0) sigma ->
      m0=m -> c0=c -> om0 m0 c0 = om m0 c0 ->
      (local_coherency p (a,CP m0 i0 c0 om0 pi0) (CP m i c om pi) /\
        strong_local_coherency p (a,CP m0 i0 c0 om0 pi0) (CP m i c om pi)))
  end.

Definition dcounter (fr:frame) (fr':frame) :=
  match fr with (CP m _ c om _, _,_) =>
    match fr' with (CP m' _ c' om' _,_,_) =>
      m=m' -> c=c' -> om' m c <> om m c
    end
  end.

Inductive lunicity : call_stack -> Prop := 
| lunicity0 : lunicity nil
| lunicity1 : forall fr cs
  (H:lunicity cs)
  (H': forall fr', In fr' cs -> dcounter fr fr'),
  lunicity (fr::cs).

Definition gunicity (L:threads) : Prop :=
  forall l l' cs cs' fr fr',  
    l<>l' -> L l = Some cs -> L l' = Some cs' ->
    In fr cs -> In fr' cs' -> dcounter fr fr'.

Lemma dcounter_sym : forall fr fr', 
  dcounter fr fr' -> dcounter fr' fr.
destruct fr as [[[m i c om pi] s] rho].
destruct fr' as [[[m' i' c' om' pi'] s'] rho'].
unfold dcounter, not.
intros.
subst.
apply H;auto. 
Qed.

Lemma dcounter_intra :
  forall m i i' c om pi pi' s s' rho rho' fr,
  dcounter (CP m i c om pi,s,rho) fr ->
  dcounter (CP m i' c om pi',s',rho') fr.
Proof.
auto.
Qed.

(* frame_coherency *)

Lemma frame_coherency_intra : forall m i c om pi s rho omg,
  frame_coherency (CP m i c om pi,s,rho) omg ->
  forall i' pi' s' rho', 
    frame_coherency (CP m i' c om pi',s',rho') omg.
Proof.
intros.
auto.
Qed.

Lemma incr_mVect_eq :
  forall omg m c,
  incr_mVect omg m c m c = S (omg m c).
Proof.
unfold incr_mVect, conv_mVect.
intros.
rewrite MVect.get_upd1; auto.
Qed.

Lemma incr_mVect_diff :
  forall omg m c m' c', ((m,c) <> (m',c')) ->
    incr_mVect omg m c m' c' = omg m' c'.
Proof.
intros.
unfold incr_mVect, conv_mVect.
rewrite MVect.get_upd2; auto.
Qed.

Lemma incr_mVect_prop :
  forall (omg:mVect) m c m' c',
    omg m' c' <= incr_mVect omg m c m' c'.
Proof.
intros.
apply incr_mVect_lt.
Qed.
Lemma frame_coherency_step : 
  forall p L sigma mu omg L' sigma' mu' omg' e,
    (forall l cs fr, L l = Some cs -> 
      In fr cs -> frame_coherency fr omg) ->
    step p (L,sigma,mu,omg) (L',sigma',mu',omg') e ->
    (forall l cs fr, L' l = Some cs -> 
      In fr cs -> frame_coherency fr omg').
Proof.
intros.
inv H0.
inv H12.
unfold upd_thread in H1.
MLtac' o l.
inj H1.
inv H15.
assert (frame_coherency fr0 omg') by (eauto using in_eq).
destruct fr0 as [[[m0 ? c0 om0 ? ] ?]?].
destruct fr' as [[[m' ? c' om' ? ] ?]?].
assert (m0=m' /\ c0=c'/\om0=om') by (inversion H10; auto).
destruct H1 as [? [? ?]]; subst.
destruct H2. subst.
assumption.
eapply H.
apply H13.
apply in_cons.
assumption.


destruct H2.
subst.
unfold frame_coherency.
simpl in *.
generalize (incr_mVect_eq omg m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0))).
intro.
rewrite H0.
unfold invoke_mVect.
unfold conv_mVect.
rewrite MVect.get_upd1.
omega.

assert (frame_coherency fr omg).
destruct H0.
subst.
assert (frame_coherency (CP m i c om pi,v_list++Loc (a0,CP m0 i0 c0 om0 pi0)::s',rho) omg).
eapply H; eauto using in_eq.
auto.
eapply H; eauto using in_cons.

destruct fr as [[[m2 i2 c2 om2 pi2]s2]rho2].
unfold frame_coherency in H1 |-*.
simpl in *.
generalize (incr_mVect_prop omg m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0)) m2 c2).
omega.

eauto using in_cons.
destruct H2.
subst.
assert (frame_coherency (p0,s',rho') omg') by
  (eauto using in_cons, in_eq).
auto.
eauto using in_cons.

assert (forall m c, omg m c <= omg' m c).
inv H15.
intros.
omega.
intros.
exact (incr_mVect_prop omg m1  (C.make_call_context m i c (C.make_new_context m0 i0 cId c0)) m2 c1).
intros; omega.
intros; omega.
assert (frame_coherency fr omg) by eauto.
destruct fr as [[[m2 i2 c2 om2 pi2]?]?].
unfold frame_coherency in H3 |-*.
simpl in *.
generalize (H0 m2 c2).
omega.

unfold upd_thread in H1.
simpl in *.
Case'.
inj H1.
destruct H2.
subst.
unfold frame_coherency.
simpl.
unfold invoke_mVect.
unfold incr_mVect.
unfold conv_mVect.
repeat rewrite MVect.get_upd1.
omega.
elim H0; reflexivity.

Case'.
inj H1.
destruct H2.
subst.
assert (frame_coherency (CP m i c om pi,Loc(a0,CP m0 i0 c0 om0 pi0)::s',rho) omg).
eauto using in_eq.
unfold frame_coherency in H0 |-*.
simpl in *.
intros.
generalize (incr_mVect_prop omg m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0)) m c).
intro.
omega.

assert (frame_coherency fr omg) by eauto using in_cons.
destruct fr as [[[m2 i2 c2 om2 pi2]s2]rho2].
unfold frame_coherency in H1 |-*.
simpl in *.
intros.
generalize (incr_mVect_prop omg m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0)) m2 c2).
intro.
omega.

assert (frame_coherency fr omg) by eauto using in_eq.
destruct fr as [[[m2 i2 c2 om2 pi2]s2]rho2].
unfold frame_coherency in H2 |-*.
simpl in *.
intros.
generalize (incr_mVect_prop omg m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0)) m2 c2).
intro.
omega.

unfold upd_thread in H1.
MLtac' o l.
inj H1.
destruct H2.
subst.
assert (frame_coherency (CP m i c om pi,Loc o'::s,rho) omg').
eauto using in_eq.
auto.
auto.
eauto using in_cons.
eauto.

unfold upd_thread in H1.
MLtac' o l.
inj H1.
destruct H2.
subst.
assert (frame_coherency (CP m i c om pi,Loc o'::s,rho) omg').
eauto using in_eq.
auto.
auto.
eauto using in_cons.
eauto.
Qed.


Lemma lunicity_intra :forall m i c om pi s rho cs,
  lunicity ((CP m i c om pi,s,rho)::cs) -> 
  forall i' pi' s' rho', 
    lunicity ((CP m i' c om pi',s',rho')::cs).
Proof.
intros.
inv H.
apply lunicity1; 
  [assumption | intros; eapply dcounter_intra; eauto].
Qed.

Lemma lunicity_invoke : forall L l cs m i c om pi s rho omg,
  (forall l cs, L l =Some cs -> lunicity cs) ->
  (forall l cs fr, L l = Some cs -> In fr cs -> frame_coherency fr omg) ->
  L l = Some ((CP m i c om pi,s,rho)::cs) ->
  forall m' i' c' (om':mVect) pi' s' rho' i'' pi'' s'' rho'',
    om' m' c' = S (omg m' c') ->
    forall l' cs', (upd_thread L l 
      ((CP m' i' c' om' pi',s',rho')::(CP m i'' c om pi'',s'',rho'')::cs)) l'
    =Some cs' -> lunicity cs'.
Proof.
intros.
unfold upd_thread in H3.
MLtac' l l'.
inj H3.
apply lunicity1.
eapply lunicity_intra;eauto.
intros.
assert (frame_coherency fr' omg).
destruct H3.
subst.
assert (frame_coherency (CP m i c om pi,s,rho) omg).
eapply H0.
apply H1.
apply in_eq.
auto.
eapply H0.
apply H1.
apply in_cons.
apply H3.
destruct fr' as [[[m0 i0 c0 om0 pi0]s0]rho0].
unfold frame_coherency in H4.
unfold dcounter.
intros.
simpl in H4.
subst.
omega.

eapply H; eauto.
Qed.

Lemma upd_thread_new : forall L l cs,
  upd_thread L l cs l = Some cs.
Proof.
  unfold upd_thread; intros.
  MLtac' l l; intuition.
Qed.

Lemma lunicity_step : 
  forall p L sigma mu omg L' sigma' mu' omg' e,
  (forall l cs, L l = Some cs -> lunicity cs) ->
  (forall cs l fr, L l = Some cs -> In fr cs -> frame_coherency fr omg) ->
  step p (L,sigma,mu,omg) (L',sigma',mu',omg') e ->
  (forall l cs, L' l = Some cs -> lunicity cs).
Proof.
intros.
inv H1.
inv H12.
unfold upd_thread in H2.
MLtac' o l.
inj H2.
inv H15.
destruct fr as [[[m ? c om ?] ? ]?].
destruct fr' as [[[m' ? c' om' ?] ? ]?].
assert (m=m'/\c=c'/\om=om') by (inversion H10; auto).
destruct H1 as [? [? ?]]; subst.
eapply lunicity_intra; eauto.

eapply lunicity_invoke;eauto using upd_thread_new.

apply H in H13.
inv H13.
unfold invoke_mVect, conv_mVect.
rewrite MVect.get_upd1.
reflexivity.

apply H in H13.
inv H13.
inv H2.
apply lunicity0.
apply lunicity1.
assumption.
intros.
apply H'0.
assumption.
generalize (H _ _ H13).
intro.
inv H1.
inv H3.
destruct p0.
apply lunicity1.
assumption.
intros.
eapply dcounter_intra.
apply H'0.
apply H1.

eauto.

unfold upd_thread in H2.

simpl in *; Case'.
inj H2.
apply lunicity1.
apply lunicity0.
intros.
destruct H1.
MLtac' o l.
inj H2.
eapply lunicity_intra.
eapply H.
apply H13.
eauto.

eauto.

unfold upd_thread in H2.
MLtac' o l.
inj H2.
apply H in H13.
inv H13.
apply lunicity1.
assumption.
intros.
eapply dcounter_intra; eauto.
eauto.

unfold upd_thread in H2.
MLtac' o l.
inj H2.
apply H in H13.
inv H13.
apply lunicity1.
assumption.
intros.
eapply dcounter_intra; eauto.
eauto.
Qed.

Lemma gunicity_intra : forall L l,
  gunicity L ->
  forall m i c om pi s rho cs,
    L l = Some ((CP m i c om pi,s,rho)::cs) ->
    forall i' pi' s' rho',
      gunicity (upd_thread L l ((CP m i' c om pi',s',rho')::cs)).
Proof.
unfold gunicity, upd_thread.
intros.
MLtac' l l0.
inj H2.
MLtac' l0 l'.
elim H1; reflexivity.
destruct H4.
subst.
eapply dcounter_intra; eauto using in_eq.
eauto using in_cons.
MLtac' l l'.
inj H3.
destruct H5.
subst.
apply dcounter_sym.
eapply dcounter_intra; eauto using in_eq.
eauto using in_cons.
eauto.
Qed.

Lemma gunicity_invoke : forall L l cs m i c om pi s rho omg,
  gunicity L ->
  (forall l cs fr, L l = Some cs -> In fr cs -> frame_coherency fr omg) ->
  L l = Some ((CP m i c om pi,s,rho)::cs) ->
  forall m' i' c' (om':mVect) pi' s' rho' i'' pi'' s'' rho'',
    om' m' c' = S (omg m' c') ->
    gunicity (upd_thread L l 
      ((CP m' i' c' om' pi',s',rho')::(CP m i'' c om pi'',s'',rho'')::cs)).
Proof.
unfold gunicity, upd_thread.
intros.
MLtac' l l0.
inj H4.
MLtac' l0 l'.
elim H3; reflexivity.
destruct H6.
subst.
assert (frame_coherency fr' omg) by eauto.
destruct fr' as [[[m0 i0 c0 om0 pi0]?]?].
unfold dcounter.
unfold frame_coherency in H4.
simpl in H4.
intros.
subst.
omega.
destruct H4.
subst.
eapply dcounter_intra.
eapply H; eauto using in_eq.
eapply H; eauto using in_cons.
MLtac' l l'.
injection H5; intros; subst; clear H5.
destruct H7.
subst.
assert (frame_coherency fr omg) by eauto.
destruct fr as [[[m0 i0 c0 om0 pi0]?]?].
unfold dcounter.
unfold frame_coherency in H5.
simpl in H5.
intros.
subst.
omega.
apply dcounter_sym.
destruct H5.
subst.
eapply dcounter_intra.
eapply H; eauto using in_eq.
eapply H; eauto using in_cons.
eauto.
Qed.

Lemma gunicity_start : forall L l l' m i c om pi s rho cs omg,
  gunicity L ->
  (forall l cs fr, L l = Some cs -> In fr cs -> frame_coherency fr omg) ->
  L l = Some ((CP m i c om pi,s,rho)::cs) ->
  L l' = None ->
  forall m' i' c' (om':mVect) pi' s' rho' i'' pi'' s'' rho'',
  om' m' c' = S(omg m' c') -> 
  gunicity 
  (upd_thread (upd_thread L l ((CP m i'' c om pi'',s'',rho'')::cs)) l'
  ((CP m' i' c' om' pi',s',rho')::nil)).
Proof.
unfold gunicity, upd_thread.
intros.
MLtac' l' l0.
inj H5.
inv H7 ; [idtac | tauto]. 

assert (frame_coherency fr' omg).
MLtac' l0 l'0; [elim H4; reflexivity | idtac].
MLtac' l l'0.
inj H6.
destruct H8.
subst.
assert (frame_coherency (CP m i c om pi,s,rho) omg) by
  (eapply H0; eauto using in_eq).
auto.
eapply H0; eauto using in_cons.
eapply H0; eauto using in_cons.

destruct fr' as [[[? ? ? ? ?]?]?].
unfold dcounter.
unfold frame_coherency in H5.
simpl in H5.
intros.
subst. 
omega.

MLtac' l' l'0.
inj H6.
destruct H8; [idtac | tauto].
subst.

assert (frame_coherency fr omg).
MLtac' l l0.
inj H5.
destruct H7.
subst.
assert (frame_coherency (CP m i c om pi,s,rho) omg) by
  (eapply H0; eauto using in_eq).
auto.
eauto using in_cons.
eauto.
destruct fr as [[[? ? ? ? ?] ?]?].
unfold dcounter.
intros.
subst.
unfold frame_coherency in H6.
simpl in H6.
omega.


MLtac' l l0.
inj H5.
MLtac' l0 l'0; [elim H4;reflexivity | idtac].
destruct H7.
subst.
eapply dcounter_intra.
eauto using in_eq.
eauto using in_cons.
MLtac' l l'0.
inj H6.
destruct H8.
subst.
apply dcounter_sym.
eapply dcounter_intra.
eauto using in_eq.
eauto using in_cons.
eauto.
Qed.

Lemma gunicity_step :
  forall p L sigma mu omg L' sigma' mu' omg' e,
  gunicity L -> 
  (forall cs l fr, L l = Some cs -> In fr cs -> frame_coherency fr omg) ->
  step p (L,sigma,mu,omg) (L',sigma',mu',omg') e ->
  gunicity L'.
Proof.
intros.
inv H1.
inv H11.
inv H14.
(* intra *)
destruct fr as [[[m i c om pi]s]rho].
destruct fr' as [[[m' i' c' om' pi']s']rho'].
assert (m=m'/\c=c'/\om=om') by (inversion H10; eauto).
destruct H1 as [?[? ?]].
subst.
eapply gunicity_intra; eauto.

(* invoke *)
eapply gunicity_invoke.
assumption.
intros.
eapply H0.
apply H1.
apply H2.
apply H12.
unfold invoke_mVect, conv_mVect.
rewrite MVect.get_upd1.
reflexivity.

(* return *)
unfold gunicity, upd_thread.
unfold gunicity in H.
intros.
MLtac' o l.
inj H2.
MLtac' l l';[elim H1;reflexivity | idtac].
eauto using in_cons.
MLtac' o l'.
inj H3.
eauto using in_cons.
eauto.

(* areturn *)

unfold gunicity, upd_thread.
unfold gunicity in H.
intros.
destruct p0.
MLtac' o l.
inj H2.
MLtac' l l'; [elim H1; reflexivity | idtac].
destruct H4.
subst; eapply dcounter_intra; eauto using in_cons, in_eq.
eauto using in_cons.
MLtac' o l'.
inj H3.
destruct H5.
subst; apply dcounter_sym; 
  eapply dcounter_intra; apply dcounter_sym;
    eauto using in_cons, in_eq.
eauto using in_cons.

eauto.
(* run *)
eapply gunicity_start;eauto.
unfold invoke_mVect, conv_mVect.
rewrite MVect.get_upd1.
reflexivity.

(* monitorenter *)
eapply gunicity_intra; eauto.
(* monitorexit *)
eapply gunicity_intra; eauto.
Qed.

End WF1.