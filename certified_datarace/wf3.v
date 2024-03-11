Require Export wf2.

Module WF3 (S:COUNTING_SEMANTIC). Import S.

  Module W2 := WF2 S. Import W2 W1 DP.

Lemma frame_coherency_incr_mVect : forall fr omg,
  frame_coherency fr omg -> forall m c,
  frame_coherency fr (incr_mVect omg m c).
Proof.
destruct fr as [[[m i c om pi]?]?].
unfold frame_coherency.
simpl.
intros.
generalize (incr_mVect_prop omg m0 c0 m c).
omega.
Qed.

Lemma global_coherency_incr_mVect : forall l omg,
  global_coherency l omg -> forall m c,
    global_coherency l (incr_mVect omg m c).
Proof.
destruct l as [a [m' i' c' om' pi']].
unfold global_coherency.
intros.
generalize (incr_mVect_prop omg m c m' c').
omega.
Qed.

Lemma fc_step  : 
  forall p L sigma mu omg L' sigma' mu' omg' e,
    (forall l cs fr, L l = Some cs -> In fr cs -> frame_coherency fr omg) ->
    step p (L,sigma,mu,omg) (L',sigma',mu',omg') e ->
    (forall l cs fr, L' l = Some cs -> In fr cs -> frame_coherency fr omg').
Proof.
intros.
inv H0.
MLtac' o l.
inv H12.
rewrite (upd_thread_new L l cs') in H1.
inj H1.
inv H15.
destruct H2.
subst.
destruct fr0 as [[[m0 i0 c0 om0 pi0]?]?].
destruct fr as [[[m i c om pi]?]?].
assert (m0=m/\c0=c/\om0=om) by (inversion H10;auto).
destruct H0 as [? [? ?]].
subst.
generalize (H l _ _ H13 (in_eq _ _)).
intro.
auto.
eapply H; eauto using in_cons.

destruct H2.
subst.
unfold frame_coherency.
simpl.
unfold invoke_mVect, incr_mVect, conv_mVect.
repeat rewrite MVect.get_upd1.
omega.

destruct H0.
subst.

unfold frame_coherency.
simpl.
unfold invoke_mVect, incr_mVect, conv_mVect.
repeat rewrite MVect.get_upd1.

generalize (incr_mVect_prop omg m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0)) m c).
intro.
generalize (H l _ _ H13 (in_eq _ _)).
intro.
unfold frame_coherency in H1.
simpl in H1.
unfold invoke_mVect, incr_mVect, conv_mVect in *.
omega.

destruct fr as [[[m2 i2 c2 om2 pi2]?]?].
generalize (incr_mVect_prop omg m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0)) m2 c2).
generalize (H l _ _ H13 (in_cons _ _ _ H0)).
intros.
unfold frame_coherency in *.
simpl in *.
omega.

eapply H; eauto using in_cons.
destruct H2.
subst.
assert ((frame_coherency (p0,s',rho') omg')) by (eapply H; eauto using in_cons, in_eq).
auto.
eapply H; eauto using in_cons.

unfold upd_thread in H1.
simpl in *; Case'.
inj H1.
destruct H2; [idtac | tauto].
subst.
unfold frame_coherency.
simpl.
rewrite (incr_mVect_eq omg m1  (C.make_call_context m i c (C.make_new_context m0 i0 cId c0))).
unfold invoke_mVect, conv_mVect in *.
rewrite MVect.get_upd1 in *.
omega.

destruct (S.eq_memloc' l l).
inj H1.
destruct H2.
subst.

unfold frame_coherency.
simpl.
generalize (incr_mVect_prop omg m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0)) m c).
intro.
generalize (H l _ _ H13 (in_eq _ _)).
intro.
unfold frame_coherency in *.
simpl in *.
omega.

destruct fr as [[[m2 i2 c2 om2 pi2]?]?].
generalize (incr_mVect_prop omg m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0)) m2 c2).
generalize (H l _ _ H13 (in_cons _ _ _ H0)).
intros.
unfold frame_coherency in *.
simpl in *.
omega.

rewrite H1 in H13.
inj H13.
assert (frame_coherency fr omg) by (eapply H; eauto).
destruct fr as [[[m2 i2 c2 om2 pi2]?]?].
generalize (incr_mVect_prop omg m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0)) m2 c2).
intros.
unfold frame_coherency in *.
simpl in *.
omega.

unfold upd_thread in H1.
destruct (S.eq_memloc' l l).
inj H1.
destruct H2.
subst.
assert (frame_coherency (CP m i c om pi,Loc o'::s,rho) omg') by (eapply H; eauto using in_eq).
auto.
eapply H; eauto using in_cons.
eapply H; eauto.

unfold upd_thread in H1.
destruct (S.eq_memloc' l l).
inj H1.
destruct H2.
subst.
assert (frame_coherency (CP m i c om pi,Loc o'::s,rho) omg') by (eapply H; eauto using in_eq).
auto.
eapply H; eauto using in_cons.
eapply H; eauto.

inv H12.
rewrite (upd_thread_old L o cs' l) in H1.
inv H15.
eapply H; eauto.
eapply frame_coherency_incr_mVect; eauto.
eapply H. 
apply H1.
assumption.

eapply H.
apply H1.
assumption.
assumption.

unfold upd_thread in H1.
simpl in *; Case'.
inj H1.
destruct H2; [idtac | tauto].
subst.
unfold frame_coherency.
simpl.
rewrite (incr_mVect_eq omg m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0))).
unfold invoke_mVect, conv_mVect.
rewrite MVect.get_upd1.
omega.
MLtac' o l.
intuition.

eapply frame_coherency_incr_mVect; eauto.

unfold upd_thread in H1.
MLtac' o l.
intuition.
eapply H; eauto.

unfold upd_thread in H1.
MLtac' o l.
intuition.
eapply H; eauto.
Qed.


Lemma gc_step : forall p L sigma mu omg L' sigma' mu' omg' e,
  (forall l, inDom l sigma -> global_coherency l omg) ->
  (forall l cs fr, L l = Some cs -> In fr cs -> frame_coherency fr omg) ->
  step p (L,sigma,mu,omg) (L',sigma',mu',omg') e ->
  (forall l, inDom l sigma' -> global_coherency l omg').
Proof.
intros.
inv H1.
inv H12.
inv H15.
inv H11.
assert (inDom l sigma) by (eapply step0_heap_domain; eauto).
eauto.
generalize (alloc_coDom sigma sigma' _ l HYP5 H2).
intro.
destruct H1.
subst.
unfold global_coherency.
generalize (H0 _ _ _ H13 (in_eq _ _)).
intro.
unfold frame_coherency in H1.
simpl in H1.
assumption.
eauto.

eapply global_coherency_incr_mVect; eauto.
eapply H; eauto.
eapply H; eauto.
eapply global_coherency_incr_mVect; eauto.
eapply H; eauto.
eapply H;eauto.
Qed.

Lemma rechable_frame_coherency : forall p st,
  reachable p st ->
  forall L sigma mu omg, st = (L,sigma,mu,omg) ->
  forall l cs fr,L l = Some cs -> In fr cs -> frame_coherency fr omg.
Proof.
induction 1.
intros.
inv H.
unfold threads_init in H0.
Case'.
inj H0.
destruct H1; [idtac | tauto].
subst.
unfold frame_coherency.
simpl.
omega.
discriminate H0.

intros.
subst.
destruct st as [[[L0 sigma0] mu0] om0].
eapply fc_step.
intros.
eapply IHreachable.
reflexivity.
apply H0.
apply H3.
apply H'.
apply H1.
apply H2.
Qed.

Lemma reachable_global_coherency : forall p st,
  reachable p st ->
  forall L sigma mu omg, st = (L,sigma,mu,omg) ->
    forall l, inDom l sigma -> global_coherency l omg.
Proof.
induction 1.
intros.
inv H.
unfold sigma_init in H0.
unfold inDom in *.
MLtac l (run_address, cp_run_address p).
unfold cp_run_address.
unfold global_coherency.
unfold om_run_address.
unfold om_init.
unfold conv_mVect.
rewrite MVect.get_init.
compute; omega.

elim H0; reflexivity.

intros.
subst.

destruct st as [[[L0 sigma0] mu0] omg0].
eapply gc_step.



generalize (IHreachable L0 sigma0 mu0 omg0 (refl_equal _)).
intro.
apply H0.
intros.
eapply rechable_frame_coherency; eauto.
eauto.
auto.
Qed.


Lemma reachable_lunicity : forall p st,
  reachable p st ->
  forall L sigma mu omg, st = (L,sigma,mu,omg) ->
    (forall l cs, L l = Some cs -> lunicity cs).
Proof.
induction 1.
intros.
inv H.
unfold  threads_init in H0.
Case'.
inj H0.
apply lunicity1.
apply lunicity0.
intros.
elim H.
discriminate H0.

intros.
subst.
destruct st as [[[L0 sigma0] mu0]omg0].
eapply lunicity_step.
intros.

subst.
eapply IHreachable.
reflexivity.
apply H0.
intros.


eapply rechable_frame_coherency; eauto.
apply H'.
eauto.
Qed.


Lemma reachable_gunicity : forall p st,
  reachable p st ->
  forall L sigma mu omg, st = (L,sigma,mu,omg) ->
    gunicity L.
Proof.
induction 1.
intros.
unfold gunicity.
intros.
inv H.
unfold threads_init in *.
Case'.
inj H1.
Case'.
elim H0; reflexivity.
discriminate.
discriminate.

intros.
destruct st as [[[L0 sigma0] mu0]omg0].
subst.
generalize (IHreachable L0 sigma0 mu0 omg0 (refl_equal _)).
intros.
eapply gunicity_step.
eapply IHreachable.
reflexivity.
intros.

eapply rechable_frame_coherency; eauto.
apply H'.
Qed.


Lemma reachable_local_coherency : forall p st,
  reachable p st -> forall L sigma mu omg,
    st = (L,sigma,mu,omg) -> 
    (forall l l' cs m i c om pi s rho, 
      L l= Some cs -> In (CP m i c om pi, s,rho) cs -> inDom l' sigma -> local_coherency p l' (CP m i c om pi)).
Proof.
induction 1.
intros.
inv H.

assert (l'=(run_address, cp_run_address p)).
unfold sigma_init in H2.
unfold inDom in H2.
MLtac l' (run_address,cp_run_address p).
reflexivity.
elim H2.
reflexivity.

assert (l=(run_address,None)).
unfold threads_init in H0.
Case'.
reflexivity.
discriminate H0.

subst.

assert ((CP m i c om pi) = (CP p.(main) 0 C.init_mcontext (om_init p) LVect.init)).
unfold threads_init in H0.
Case'.
inj H0.
destruct H1; [idtac | tauto].
unfold cp_run_address in H.
symmetry.
inversion H.
reflexivity.
discriminate H0.
rewrite H.
unfold cp_run_address.
unfold local_coherency.
omega.


intros.
subst.
destruct st as [[[L0 sigma0]om0]pi0].
eapply lc_step.
intros.
eapply reachable_global_coherency; eauto.
intros.
eapply reachable_lunicity;eauto.
eapply reachable_gunicity;eauto.
intros.
eapply IHreachable; eauto.
apply H'.
apply H1.
apply H2.
apply H3.
Qed.

Lemma reachable_def : forall p st,
  reachable p st -> forall L sigma mu omg,
  st = (L,sigma,mu,omg) ->
  (forall l cs cp s rho, L l = Some cs -> In (cp,s,rho) cs -> exists cl, In cl (classes p) /\ In (cp_m cp) (methods cl)).
Proof.
induction 1.
intros.
inv H.
unfold threads_init in *.
Case'.
inv H0.
destruct H1.
inj H.
exists (main_class p).
split.
apply main_class_prop.
unfold cp_init.
simpl.
apply main_prop_1.
intuition.
discriminate.

intros.
inv H'.
assert (IH:=IHreachable _ _ _ _ (refl_equal _)); clear IHreachable.
inj H6.
destruct (eq_memloc' o l).
subst.
inv H3.
rewrite upd_thread_new in H1.
inj H1.
inv H15.
destruct fr as [[[m1 i1 c1 om1 pi1] s1] rho1].
generalize (IH l ((CP m1 i1 c1 om1 pi1,s1,rho1)::cs0)).
intro IHreachable.
destruct H2.
generalize (IHreachable (CP m1 i1 c1 om1 pi1) s1 rho1 H4 (in_eq _ _)).
intro.
subst.
destruct cp as [m2 i2 c2 om2 pi2].
assert (m1=m2) by (inversion H11;auto).
subst.
simpl in *.
assumption.
assert (In (cp,s,rho) ((CP m1 i1 c1 om1 pi1,s1,rho1)::cs0)) by (eauto using in_cons).
generalize (IHreachable cp s rho H4 H1).
auto.

destruct H2.
inj H0.
simpl.
apply p.(lookup_prop_1) in H12.
destruct H12 as [cl [? [? [? ?]]]].
exists cl.
auto.

destruct H0.
inj H0.
generalize (IH _ _ _ _ _ H4 (in_eq _ _)).
intro.
simpl in *.
assumption.

assert (In (cp,s,rho) ((CP m i c om pi, v_list++(Loc (a0, CP m0 i0 c0 om0 pi0))::s',rho0)::cs0)) by
  (eauto using in_cons).

generalize (IH _ _ _ _ _ H4 H1).
auto.

assert (In (cp,s,rho) ((CP m i c om pi,s,rho)::cs)) by
  (eauto using in_cons).
eapply IH;eauto using in_cons.

destruct H2.
inj H0.

assert (In (cp,s',rho) ((CP m i c om pi,v::s0,rho0)::(cp,s',rho)::cs1)).
eauto using in_cons, in_eq.

generalize (IH _ _ _ _ _ H4 H0). 
auto.

eapply IH;eauto using in_cons.

unfold upd_thread in *.
simpl in *; Case'.
subst.
inv H1.
congruence.
destruct (S.eq_memloc' l l).
inv H1.

destruct H2.
inj H0.
assert (In (CP m i c om pi,Loc(a0,CP m0 i0 c0 om0 pi0)::s,rho) 
  ((CP m i c om pi,Loc(a0,CP m0 i0 c0 om0 pi0)::s,rho)::cs0)).
apply in_eq.
generalize (IH _ _ _ _ _ H4 H0).
intro.
simpl in *.
assumption.
assert (In (cp,s,rho) ((CP m i c om pi,Loc(a0,CP m0 i0 c0 om0 pi0)::s',rho0)::cs0)).
auto using in_cons.
generalize (IH _ _ _ _ _ H4 H1).
auto.
intuition.

unfold upd_thread in *.
destruct (S.eq_memloc' l l); [idtac|intuition].
inv H1.
destruct H2.
inj H0.
assert (In (CP m i c om pi,Loc o'::s,rho) ((CP m i c om pi,Loc o'::s,rho)::cs0))
  by (auto using in_eq).
generalize (IH _ _ _ _ _ H4 H0).
simpl.
auto.
assert (In (cp,s,rho) ((CP m i c om pi,Loc o'::s0,rho0)::cs0)) by
  (eauto using in_cons).
generalize (IH _ _ _ _ _ H4 H1).
auto.

unfold upd_thread in *.
destruct (S.eq_memloc' l l); [idtac|intuition].
inv H1.
destruct H2.
inj H0.
assert (In (CP m i c om pi,Loc o'::s,rho) ((CP m i c om pi,Loc o'::s,rho)::cs0))
  by (auto using in_eq).
generalize (IH _ _ _ _ _ H4 H0).
simpl.
auto.
assert (In (cp,s,rho) ((CP m i c om pi,Loc o'::s0,rho0)::cs0)) by
  (eauto using in_cons).
generalize (IH _ _ _ _ _ H4 H1).
auto.

inv H3.
unfold upd_thread in *.
destruct (S.eq_memloc' o l); [intuition|idtac].
generalize (IH _ _ _ _ _ H1 H2).
auto.

unfold upd_thread in *.
simpl in *; Case'.
inv H1.
destruct H2.
inj H0.
simpl.
apply p.(lookup_prop_1) in H18.
destruct H18 as [cl [? [? [? ?]]]].
exists cl.
auto.
intuition.

destruct (S.eq_memloc' o l); [intuition|idtac].
generalize (IH _ _ _ _ _ H1 H2).
auto.

unfold upd_thread in *.
destruct (S.eq_memloc' o l); [intuition|idtac].
generalize (IH _ _ _ _ _ H1 H2).
auto.


unfold upd_thread in *.
destruct (S.eq_memloc' o l); [intuition|idtac].
generalize (IH _ _ _ _ _ H1 H2).
auto.
Qed.


Lemma reachable_strong_local_coherency : forall p st,
  reachable p st -> 
  safe_loop p ->
  forall L sigma mu omg,
    st = (L,sigma,mu,omg) -> 
    (forall l l' cs m i c om pi s rho, 
      L l= Some cs -> In (CP m i c om pi, s,rho) cs -> inDom l' sigma -> strong_local_coherency p l' (CP m i c om pi)).
Proof.
induction 1.
intros.
inv H0.

assert (l'=(run_address, cp_run_address p)).
unfold sigma_init in H3.
unfold inDom in H3.
MLtac l' (run_address,cp_run_address p).
reflexivity.
elim H3.
reflexivity.

assert (l=(run_address,None)).
unfold threads_init in H1.
Case'.
reflexivity.
discriminate H1.

subst.

assert ((CP m i c om pi) = (CP p.(main) 0 C.init_mcontext (om_init p) LVect.init)).
unfold threads_init in H1.
Case'.
inj H1.
destruct H2; [idtac | tauto].
unfold cp_init in H0.
symmetry.
inversion H0.
reflexivity.
discriminate H1.

rewrite H0.
unfold cp_run_address.
unfold strong_local_coherency.
intros.
unfold om_init in H6.
unfold om_run_address in H6.
unfold conv_mVect in *.
rewrite H4 in *.
rewrite MVect.get_upd1 in *.
rewrite MVect.get_init in *.
discriminate H6.

intros.
subst.
destruct st as [[[L0 sigma0] mu0] omg0].
eapply slc_step.
assumption.
intros.
eapply reachable_lunicity;eauto.
eapply reachable_gunicity;eauto.
intros.
eapply reachable_local_coherency;eauto.
intros.
eapply reachable_global_coherency;eauto.
intros.
eapply reachable_def.
apply H.
reflexivity.
apply H1.
apply H5.
intros.
destruct cp as [m0 i0 c0 om0 pi0].
eapply IHreachable; eauto.
apply H'.
apply H2.
apply H3.
apply H4.
Qed.

Definition coherent (p:program) (st:state) :=
  match st with (L,sigma,mu,omg) =>
    forall a a' m i c om om' pi pi',
      inDom (a,CP m i c om pi) sigma -> 
      inDom (a', CP m i c om' pi') sigma ->
      om m c = om' m c ->
      pi m c (loop p (m,i)) = pi' m c (loop p (m,i)) ->
      a=a'
  end.

Lemma coherent_reduce : forall p st st' e,
  reachable p st ->
  safe_loop p ->
  coherent p st ->  
  step p st st' e ->
  coherent p st'.
Proof.
intros.
unfold coherent.
intros.
inversion H2;try (subst;clear H2).
intros.

destruct fr as [[[m0 i0 c0 om0 pi0] ? ] ?].
elim step3_heap_domain with (1:=H3).
intros fresh' H8.
apply H8 in H2.
apply H8 in H5.
destruct H2 as [Ha | Ha]; destruct H5 as [Hb | Hb].

unfold coherent in H1.
eapply H1; [apply Ha | apply Hb | assumption | assumption].

destruct Hb as [V Hb]. 
injection Hb.
intros.
subst.
clear Hb.
assert (strong_local_coherency p (a,CP m0 i0 c0 om pi) (CP m0 i0 c0 om0 pi0)).
eapply reachable_strong_local_coherency;eauto.
apply in_eq.
unfold strong_local_coherency in H2.
symmetry in H6.
destruct (H2 (refl_equal _) (refl_equal _) H6 H7).
elim H5.
reflexivity.

destruct Ha as [V Ha]. 
injection Ha.
intros.
subst.
clear Ha.
assert (strong_local_coherency p (a',CP m0 i0 c0 om' pi') (CP m0 i0 c0 om0 pi0)).
eapply reachable_strong_local_coherency;eauto.
apply in_eq.
unfold strong_local_coherency in H2.
symmetry in H7.
destruct (H2 (refl_equal _) (refl_equal _) H6 H7).
elim H5.
reflexivity.

destruct Hb as [V Hb]. 
destruct Ha as [V' Ha].
congruence.
Qed.

Theorem unicity : forall p, safe_loop p ->
  forall st, reachable p st -> coherent p st.
Proof.
induction 2.
unfold init.

unfold coherent.
intros.
assert (a=run_address).
unfold sigma_init in H0.
unfold inDom in H0.
MLtac (a,CP m i c om pi) (run_address,cp_run_address p).
inj e.
reflexivity.
elim H0.
reflexivity.

unfold coherent.
intros.
assert (a'=run_address).
unfold sigma_init in H1.
unfold inDom in H1.
MLtac (a',CP m i c om' pi') (run_address,cp_run_address p).
inj e.
reflexivity.
elim H1.
reflexivity.
subst.
reflexivity.

eapply coherent_reduce;eauto.
Qed.

End WF3.