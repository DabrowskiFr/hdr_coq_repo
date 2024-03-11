Require Export wf1.

Module WF2 (S:COUNTING_SEMANTIC).

  Module W1 := WF1 S.
  Import W1 S.

Lemma incr_lVect_eq :
  forall pi m c i j,
  incr_lVect pi m c (i,j) m c (i,j) = S(pi m c (i,j)).
Proof.
intros.
unfold incr_lVect, conv_lVect.
rewrite LVect.get_upd1; auto.
Qed.

Lemma incr_lVect_diff :
  forall pi m c fl fl',
    fl<>fl' ->
    (incr_lVect pi m c fl) m c fl' = pi m c fl'. 
Proof.
intros.
unfold incr_lVect.
unfold incr_lVect, conv_lVect.
rewrite LVect.get_upd2; congruence.
Qed.

Lemma incr_lVect_prop :
  forall (pi:lVect) m m' c c' fl fl',
  pi m c fl <= incr_lVect pi m' c' fl' m c fl.
Proof.
intros.
unfold incr_lVect.
unfold incr_lVect, conv_lVect.
destruct (excluded_middle ((m,c,fl)=(m',c',fl'))); subst.
inv H.
rewrite LVect.get_upd1; auto.
rewrite LVect.get_upd2; auto.
Qed.

Lemma lc_old_value :
  forall p l m i c om pi j,
  local_coherency p l (CP m i c om pi) ->
(*  cflow m (i,j) ->*)
  local_coherency p l (CP m j c om (incr_lVect pi m c (i,j))).
Proof.
intros.
destruct l as [? c0].
destruct c0 as [m0 i0 c0 om0 pi0].
unfold local_coherency in *.
intros.
generalize (H H0 H1 H2).
generalize (incr_lVect_prop pi m0 m c0 c (loop p (m0,i0)) (i,j)).
omega.
Qed.

Lemma lc_new_value (p:program) (cp:code_pointer) :
  match cp with (CP m i c om pi) =>
    forall  a ,    
      local_coherency p (a,CP m i c om pi) (CP m (S i) c om (incr_lVect pi m c (i,S i)))
  end.
Proof.
intros.
destruct cp as [m i c om pi].
intros.
unfold local_coherency.
intros.
apply incr_lVect_prop.
Qed.

Lemma step0_heap_domain :
  forall o ppt instr i s rho sigma i' s' rho' sigma' e,
  step0 o ppt instr (i,s,rho,sigma) (i',s',rho',sigma') e ->
  forall l, inDom l sigma' -> inDom l sigma.
Proof.
intros.
inv H; eauto.
inv HYP2.
unfold inDom in *.
destruct H as [m [Ha Hb]].
generalize (H1 l); intro.
destruct (excluded_middle (o1=l)).
subst.
rewrite Ha.
discriminate.
rewrite <- (H H2).
assumption.
Qed.

Lemma step1_heap_domain :
  forall l m i c om pi s rho sigma i' pi' s' rho' sigma' e,
  step1 l ((CP m i c om pi,s,rho),sigma) 
  ((CP m i' c om pi',s',rho'),sigma') e ->
  exists a, forall l, inDom l sigma' -> 
    inDom l sigma \/ fresh sigma a /\ l= (a,CP m i c om pi).
Proof.
intros.
inv H.
exists 1%positive.
left.
eapply step0_heap_domain; eauto.
inv HYP5.
exists a.
destruct H0 as [Ha Hb].
intros.
destruct (excluded_middle ((a, CP m i c om pi)=l0)).
eauto.
left.
unfold inDom in *.
assert (sigma' l0=sigma l0) by auto.
rewrite <- H2.
assumption.
Qed.

Lemma step3_heap_domain :
  forall p L l m i c om pi s rho cs sigma mu omg L' sigma' mu' omg' e,
  step3 p L (l,(CP m i c om pi,s,rho)::cs,sigma,mu,omg)
  (L',sigma',mu',omg') e ->
  exists a, (forall l, inDom l sigma' -> inDom l sigma \/
     fresh sigma a /\ l=(a,CP m i c om pi)).
Proof.
intros.
inv H; try (exists 1%positive; left;assumption).
inv H11;try (exists 1%positive; left;assumption).
destruct fr' as [[[m' ? c' om' ?]?]?].
assert (m=m'/\c=c'/\om=om') by (inversion H8;auto).
destruct H as [?[? ?]]; subst.
eapply step1_heap_domain; eauto.
Qed.

Ltac discriminate2 H H' := 
  rewrite H in H'; discriminate H'.

Lemma upd_thread_old : forall L l cs l',
  l<>l' -> upd_thread L l cs l' = L l'.
Proof.
  unfold upd_thread; intros.
  MLtac' l l'; intuition.
Qed.

Lemma lc_step :
  forall p L sigma mu omg L' sigma' mu' omg' e,
    (forall l, inDom l sigma -> global_coherency l omg) ->
    (forall l cs, L l =Some cs -> lunicity cs) ->
    gunicity L ->
  (forall l l' cs m i c om pi s rho, 
    L l = Some cs -> In (CP m i c om pi,s,rho) cs -> 
    inDom l' sigma -> local_coherency p l' (CP m i c om pi)) ->
  step p (L,sigma,mu,omg) (L',sigma',mu',omg') e ->
  (forall l l' cs m i c om pi s rho, 
    L' l = Some cs -> In (CP m i c om pi,s,rho) cs -> 
    inDom l' sigma' -> local_coherency p l' (CP m i c om pi)).
Proof.
intros until e.
intros HGCoherency HLUnicity HGUnicity HLCoherency HStep. 
intros.


inv HStep.
generalize (HLUnicity o (fr::cs0) H12). 
intro HLUnicity_active_thread.

destruct fr as [[[m0 i0 c0 om0 pi0] s0]rho0].
elim step3_heap_domain with (1:=H11).
intros a HD.

(* Par cas sur le thread considÃ©rÃ© *)
MLtac' o l.
(* cas thread actif *)
(* Par cas sur la rÃ¨gle de rÃ©duction *)
inv H11.
(* cas inter-procedural*)
rewrite upd_thread_new in H.
inv H.

inv H15.
(* cas intra-procedural *)
destruct fr' as [[[m1 i1 c1 om1 pi1]s1]rho1].
assert (m0=m1/\c0=c1/\om0=om1) by (inversion H10;auto).
destruct H as [?[? ?]].
assert (pi1=incr_lVect pi0 m1 c1 (i0,i1)) by (inversion H10;auto).
clear H10.
subst.

(* par cas sur la frame considÃ©rÃ©e *)
destruct H0.
(* cas frame active *)
inj H.
(* par cas sur l'adresse *)
destruct (HD _ H1).
(* ancienne addresse *)
eapply lc_old_value; eauto using in_eq.
(* nouvelle addresse *)
destruct H; subst.
unfold local_coherency.
intros; subst.
apply incr_lVect_prop.
(* cas frame passive *)
(* par cas sur l'adresse *)
destruct (HD _ H1).
(* cas ancienne adresse *)
eauto using in_cons.
(* cas nouvelle adresse *)
inv HLUnicity_active_thread.
unfold local_coherency.
intros.
destruct H0; subst.
intros; subst.
absurd (om m1 c1 <> om1 m1 c1).
auto.
generalize (H' (CP m1 i c1 om pi,s,rho) H).
auto.

(* cas invoke *)
(* par cas sur l'adresse *)
destruct (HD _ H1).
(* ancienne adresse *)
(* par cas sur la frame considÃ©rÃ©e *)
destruct H0.
(* cas nouvelle frame *)
inj H0.


apply HGCoherency in H.
destruct l' as [a' [m3 i3 c3 om3 pi3]].
unfold global_coherency in H.
unfold local_coherency.
intros.
subst.
unfold invoke_mVect, conv_mVect in *.
rewrite MVect.get_upd1 in H3.
omega.


destruct H0.
(* cas frame active *)
inj H0.
eapply lc_old_value; eauto using in_eq.
eapply HLCoherency; eauto using in_cons.

(* nouvelle adresse *)
destruct H; subst.
subst.
assert (~inDom (a,CP m0 i0 c0 om0 pi0) sigma')
  by (apply H; auto).
tauto.



(* cas return *)
eapply HLCoherency; eauto using in_cons.
(* cas areturn *)
destruct H0.
inv H.
eapply HLCoherency; eauto using in_cons, in_eq.
eapply HLCoherency; eauto using in_cons.


(* cas run *)
unfold upd_thread in H.
simpl in *; Case'.
rewrite H30 in H12; discriminate.
MLtac' l l;[idtac | tauto].
inj H.

destruct (HD _ H1).
(*cas ancienne addresse *)
destruct H0.
inj H0.
eapply lc_old_value.
eapply HLCoherency; eauto using in_eq.
eapply HLCoherency; eauto using in_cons.
(* cas nouvelle adresse *)
subst.
destruct H.
assert (~inDom (a,CP m0 i0 c0 om0 pi0) sigma')
  by (apply H; auto).
elim H3; subst; auto.

(* cas monitorenter*)
unfold upd_thread in H.
MLtac' l l; [idtac | tauto].
inj H.
destruct (HD _ H1).
destruct H0.
inj H0.
eapply lc_old_value.
eapply HLCoherency; eauto using in_eq.
eapply HLCoherency; eauto using in_cons.
destruct H.

subst.
assert (~inDom (a,CP m0 i0 c0 om0 pi0) sigma')
  by (apply H; auto).
tauto.

(* cas monitorexit*)
unfold upd_thread in H.
MLtac' l l; [idtac | tauto].
inj H.
destruct (HD _ H1).
destruct H0.
inj H0.
eapply lc_old_value.
eapply HLCoherency; eauto using in_eq.
eapply HLCoherency; eauto using in_cons.
destruct H.

subst.
assert (~inDom (a,CP m0 i0 c0 om0 pi0) sigma')
  by (apply H; auto).
tauto.

(* cas thread inactif *)

inv H11.
(* step2 *)
rewrite (upd_thread_old L o cs' l) in H.
destruct (HD _ H1) as [V|[V1 V2]].
eapply HLCoherency; eauto.
subst.
unfold gunicity in HGUnicity.
assert (dcounter (CP m0 i0 c0 om0 pi0,s0,rho0) (CP m i c om pi,s,rho)).
eapply HGUnicity; eauto using in_eq.
unfold dcounter in H2.

unfold local_coherency.
intros.
subst.
generalize (H2 (refl_equal _) (refl_equal _)).
tauto.
assumption.

(* run *)
unfold upd_thread in H.
simpl in H; Case'.
(* nouveau thread *)
inj H.
destruct H0; [idtac | tauto].
inj H.
destruct (HD _ H1) as [V|[V1 V2]].
(* ancienne adresse *)
apply HGCoherency in H1.
destruct l' as [a' [m3 i3 c3 om3 pi3]].
unfold global_coherency in H1.
unfold local_coherency.
intros.
subst.
unfold invoke_mVect, conv_mVect, conv_lVect in *.
rewrite MVect.get_upd1 in H2.
omega.
(* nouvelle adresse *)
subst.
assert (~inDom (a,CP m0 i0 c0 om0 pi0) sigma')
  by (apply V1; auto).
tauto.

(* ancien thread *)
MLtac' o l.
intuition.
eapply HLCoherency with (l:=l); eauto.


(* monitorenter *)
assert (Some cs=L l).
rewrite <- H.
apply upd_thread_old; auto.
eapply HLCoherency with (l:=l); eauto.

(* monitorenter *)
assert (Some cs=L l).
rewrite <- H.
apply upd_thread_old; auto.
eapply HLCoherency with (l:=l); eauto.
Qed.

Lemma leads_to_prop : 
  forall i j l m,
    leads_to i j l m -> exists l', l=i::l'.
Proof.
  intros.
  destruct H.
  exists (j::nil); reflexivity.
  exists l.
  reflexivity.
Qed.
Lemma list1 : 
  forall (A:Type) (l:list A) (k:nat) (v:A),
  nth_error l k = value v -> k < length l.
Proof.
induction l.
intros.
destruct k; simpl in H; discriminate H.
intros.
destruct k;simpl in *. auto with arith.
assert (k < length l).
eapply IHl.
apply H.
auto with arith.
Qed.
Lemma singleton : 
  forall a b k v v':nat,
    nth_error (a::b::nil) k = value v ->
    nth_error (a::b::nil) (S k) = value v' -> v=a /\ v'=b.
Proof.
intros.
assert (k=0).
assert (S k = 1).
apply list1 in H0.
simpl in H0.
omega.
omega.
rewrite H1 in *|-.
simpl in *|-.
injection H.
injection H0.
intros.
auto.
Qed.

Lemma local_coherency_scase (p:program) (l:memory_location) (cp:code_pointer) :
  match l with (a, CP m0 i0 c0 om0 pi0) =>
    match cp with (CP m i c om pi) =>
      forall j,
        local_coherency p l cp ->
        m=m0 -> c=c0 -> om m0 c0 = om0 m0 c0 ->
        pi0 m0 c0 (p.(loop) (m0,i0)) = 
        (incr_lVect pi m0 c0 (i,j)) m0 c0 (p.(loop) (m0,i0)) -> 
        (i,j) <> p.(loop) (m0,i0)
    end
  end. 
Proof.
destruct l as [ a c ].
destruct c as [m0 i0 c0 om0 pi0].
intros cp0.
destruct cp0 as [m i c om pi].
intros.
unfold local_coherency in H.
generalize (H H0 H1 H2).
intros.
rewrite H3 in H4.
intro.
generalize (incr_lVect_eq pi m c i j).
intro.
subst.
rewrite H5 in *.
rewrite <- H3 in H6.
omega.
Qed.

Lemma slc_old_value :
  forall p l m i c om pi j,
    local_coherency p l (CP m i c om pi) ->
    strong_local_coherency p l (CP m i c om pi) ->
    cflow m (i,j) ->
    strong_local_coherency p l (CP m j c om (incr_lVect pi m c (i,j))).
Proof.
intros.
destruct l as [a0 [m0 i0 c0 om0 pi0]].
unfold strong_local_coherency.
intros.
subst.

assert ((i,j) <> p.(loop) (m0,i0)).
generalize (local_coherency_scase p 
  (a0,CP m0 i0 c0 om0 pi0) (CP m0 i c0 om pi)).
intros.
apply H2; auto.

split.

intro.
subst.
unfold strong_local_coherency in H0.
destruct H0 as [Hyp1 Hyp2].
reflexivity.
reflexivity.
assumption.
rewrite H5.
apply incr_lVect_diff.
assumption.

destruct (Hyp2 (i::j::nil)) as [k [ik [jk[Hd[He Hf]]]]].
apply leads_to1.
assumption.
destruct (singleton i j k ik jk Hd He).
subst.
elim H2.
assumption.

intros.
destruct (leads_to_prop j i0 path m0 H3) as [l' ?].
replace path in *.
assert (leads_to i i0 (i::j::l') m0).
eapply leads_to2. apply H1.
assumption.

destruct H0 as [Hyp1 Hyp2];auto.
rewrite H5.
apply incr_lVect_diff.
assumption.

destruct (Hyp2 (i::j::l')) as [k [ik [jk [Hd [He Hf]]]]].
assumption.

 assert (exists k', k =S k').
 destruct k.
 simpl in Hd.
 simpl in He.
 injection Hd.
 injection He.
 intros.
 subst.
 elim H2.
 assumption.
 exists k.
 reflexivity.

 destruct H0 as [k' ?].
 rewrite H0 in Hd.
 rewrite H0 in He.
 simpl in Hd, He.
 
 exists k'. exists ik. exists jk.
 auto.
Qed.

Lemma step0_cflow :
  forall l m i c instr s rho sigma i' s' rho' sigma' e,
    m.(body) i = Some instr ->
    step0 l (m,i,c) instr (i,s,rho,sigma) (i',s',rho',sigma') e ->
    cflow m (i,i').
Proof.
intros.
inv H0.
eapply cflow_aconstnull; eauto.
eapply cflow_aload;eauto.
eapply cflow_astore;eauto.
eapply cflow_getfield;eauto.
eapply cflow_putfield;eauto.
eapply cflow_ifndr;eauto.
eapply cflow_ifndl;eauto.
eapply cflow_goto;eauto.
Qed.


Lemma slc_step :  forall p L sigma mu omg L' sigma' mu' omg' e,
  (safe_loop p) ->
  (forall l cs, L l = Some cs -> lunicity cs) ->
  gunicity L ->
  (forall l l' cs m i c om pi s rho, 
    L l = Some cs -> In (CP m i c om pi,s,rho) cs -> 
    inDom l' sigma -> local_coherency p l' (CP m i c om pi)) ->
  (forall l, inDom l sigma -> global_coherency l omg) -> 
  (forall l cs cp s rho,
    L l = Some cs -> In (cp,s,rho) cs -> exists cl, In cl p.(classes) /\ In (cp_m cp) cl.(methods)) ->
  (forall l cs cp s rho l',
    L l = Some cs -> In (cp,s,rho) cs -> inDom l' sigma -> strong_local_coherency p l' cp) ->
  step p (L,sigma,mu,omg) (L',sigma',mu',omg') e ->
  (forall l cs cp s rho l',
    L' l = Some cs -> In (cp,s,rho) cs -> inDom l' sigma' -> strong_local_coherency p l' cp).
Proof.
intros until e.
intros HSafeLoop HLUnicity HGUnicity HLCoherency HGCoherency HDefMethod HSLCoherency HStep.
intros.

inv HStep.
generalize (HLUnicity o (fr::cs0) H12). 
intro HLUnicity_active_thread.

destruct fr as [[[m0 i0 c0 om0 pi0] s0]rho0].
elim step3_heap_domain with (1:=H11).
intros a HD.
assert (HDomain:=HD _ H1); clear HD.

(* Par cas sur le thread considéré *)
MLtac' o l.
(* par cas sur la règle de réduction *)
inv H11.
(* cas inter-procedural *)
rewrite (upd_thread_new L l cs') in H.
inj H.
inv H15.
(* cas intra-procedural *)
destruct fr' as [[[m1 i1 c1 om1 pi1]s1]rho1].
assert (m0=m1/\c0=c1/\om0=om1) by (inversion H10;auto).
destruct H as [?[? ?]].
assert (pi1=incr_lVect pi0 m1 c1 (i0,i1)) by (inversion H10;auto).
assert (cflow m0 (i0,i1)).
inv H10.
eapply step0_cflow; eauto.
eapply cflow_new; eauto.
subst.

(* par cas sur la frame considérée *)
destruct H0.
(* cas frame active *)
inj H.
(* par cas sur l'adresse *)
destruct HDomain.
(* ancienne addresse *)
eapply slc_old_value; eauto using in_eq.

(* nouvelle addresse *)
inv H10.
destruct H as [V1 V2].
subst; simpl.
intros; subst.
assert (inDom (a, CP m1 i0 c1 om1 pi0) sigma).
eapply step0_dom_eq; eauto.
generalize (V1 (CP m1 i0 c1 om1 pi0)).
intro.
elim H6; assumption.

destruct H as [V1 V2].
subst.
unfold strong_local_coherency.
intros.
split.
auto with arith.
intros.
assert (exists cl, In cl (classes p) /\ In (cp_m (CP m1 i0 c1 om1 pi0)) (methods cl)).
eapply HDefMethod;eauto using in_eq.
unfold safe_loop in HSafeLoop.
destruct H6 as [? [? ?]].
eapply HSafeLoop; eauto.
eapply leads_to2.
eapply cflow_new; eauto.
apply H4.


destruct HDomain.
eapply HSLCoherency; eauto using in_cons.
subst.

destruct H0 as [V1 V2]; subst.
inv HLUnicity_active_thread.
destruct cp.
unfold strong_local_coherency.
intros.
subst.
absurd (cp_om m1 c1 <> om1 m1 c1).
auto.
generalize (H' (CP m1 cp_i c1 cp_om cp_pi,s,rho) H).
auto.

(* invoke *)
(* par cas sur l'adresse *)
destruct HDomain.
(* ancienne adresse *)
(* par cas sur la frame considérée *)
destruct H0.
(* cas nouvelle frame *)
inj H0.


apply HGCoherency in H.
destruct l' as [a' [m3 i3 c3 om3 pi3]].
unfold global_coherency in H.
unfold strong_local_coherency.
intros.
subst.
assert (False).
unfold invoke_mVect, conv_mVect in *.
rewrite MVect.get_upd1 in *.
omega.
elim H0; reflexivity.

destruct H0.
inj H0.

eapply slc_old_value; eauto using in_eq.
eapply cflow_invoke;eauto.

eapply HSLCoherency; eauto using in_cons.

(* nouvelle addresse *)

destruct H as [V1 V2]; subst.
assert (~inDom (a,CP m0 i0 c0 om0 pi0) sigma')
  by (apply V1; auto).
tauto.

eapply HSLCoherency; eauto using in_cons.

destruct H0.
inv H.
eapply HSLCoherency; eauto using in_cons, in_eq.
eapply HSLCoherency; eauto using in_cons.

(* run *)

unfold upd_thread in H.
simpl in *; Case'.
rewrite H30 in H12; discriminate.
MLtac' l l;[idtac | tauto].
inj H.

destruct HDomain.
(*cas ancienne addresse *)
destruct H0.
inj H0.
eapply slc_old_value.
eapply HLCoherency; eauto using in_eq.
eapply HSLCoherency; eauto using in_eq.
apply cflow_start; auto.
eapply HSLCoherency; eauto using in_cons.
(* cas nouvelle adresse *)
destruct H as [V1 V2].
subst.
assert (~inDom (a,CP m0 i0 c0 om0 pi0) sigma')
  by (apply V1; auto).
tauto.

(* cas monitorenter*)
unfold upd_thread in H.
MLtac' l l; [idtac | tauto].
inj H.
destruct HDomain.
destruct H0.
inj H0.
eapply slc_old_value.
eapply HLCoherency; eauto using in_eq.
eapply HSLCoherency; eauto using in_eq.
apply cflow_monitorenter; auto.
eapply HSLCoherency; eauto using in_cons.

destruct H as [V1 V2].
subst.
assert (~inDom (a,CP m0 i0 c0 om0 pi0) sigma')
  by (apply V1; auto).
tauto.

(* cas monitorexit*)
unfold upd_thread in H.
MLtac' l l; [idtac | tauto].
inj H.
destruct HDomain.
destruct H0.
inj H0.
eapply slc_old_value.
eapply HLCoherency; eauto using in_eq.
eapply HSLCoherency; eauto using in_eq.
apply cflow_exit; auto.
eapply HSLCoherency; eauto using in_cons.

destruct H as [V1 V2]; subst.
assert (~inDom (a,CP m0 i0 c0 om0 pi0) sigma')
  by (apply V1; auto).
tauto.

(* thread inactif *)

inv H11.
(* step2 *)
rewrite (upd_thread_old L o cs' l) in H.
destruct HDomain.
eapply HSLCoherency; eauto.
subst.
unfold gunicity in HGUnicity.
destruct cp as [m i c om pi].
assert (dcounter (CP m0 i0 c0 om0 pi0,s0,rho0) (CP m i c om pi,s,rho)).
eapply HGUnicity; eauto using in_eq.
unfold dcounter in H3.

destruct H2 as [V1 V2]; subst.
unfold strong_local_coherency.
intros.
subst.
generalize (H3 (refl_equal _) (refl_equal _)).
tauto.
assumption.

(* run *)
unfold upd_thread in H.
simpl in *; Case'.
(* nouveau thread *)
inj H.
destruct H0; [idtac | tauto].
inj H.
destruct HDomain.
(* ancienne adresse *)
apply HGCoherency in H.
destruct l' as [a' [m3 i3 c3 om3 pi3]].
unfold global_coherency in H.
unfold strong_local_coherency.
intros.
subst.
assert (False).
unfold invoke_mVect, conv_mVect in *.
rewrite MVect.get_upd1 in *.
omega.
elim H0.

(* nouvelle adresse *)
destruct H as [V1 V2]; subst.
subst.
assert (~inDom (a,CP m0 i0 c0 om0 pi0) sigma')
  by (apply V1; auto).
tauto.

(* ancien thread *)
MLtac' o l.
intuition.
eapply HSLCoherency with (l:=l); eauto.


(* monitorenter *)
assert (Some cs=L l).
rewrite <- H.
apply upd_thread_old; auto.
eapply HSLCoherency with (l:=l); eauto.

(* monitorexit *)
assert (Some cs=L l).
rewrite <- H.
apply upd_thread_old; auto.
eapply HSLCoherency with (l:=l); eauto.
Qed.

End WF2.