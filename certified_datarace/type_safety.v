Require Export types.
Require Export wf3.
(* properties of subtyping *)

Module TypeSafety (S:COUNTING_SEMANTIC).
  Module W3 := WF3 S.
  Module T := Types S.
  Import W3 W2 W1 DP T S.


Lemma eq_min : forall w, lcinf eq w.
compute; trivial.
Qed.

Lemma unknow_max : forall w, lcinf w unknown.
Proof.
intro.
unfold lcinf.
case w.
trivial.
reflexivity.
Qed.


Lemma eq_inf : forall w, lcinf w eq -> w=eq.
Proof.
intro; case w; auto.
Qed.

Lemma lcinf_refl : forall w, lcinf w w.
Proof.
intro.
unfold lcinf.
case w; auto.
Qed.


Lemma lcinf_trans : forall w w' w'',
  lcinf w w' -> lcinf w' w'' -> lcinf w w''.
Proof.
unfold lcinf.
intros.
destruct w.
assumption.
destruct w'.
discriminate H.
assumption.
Qed.

Lemma labstract_mVect_refl : forall Om,
  labstract_mVect Om Om.
Proof.
intros.
unfold labstract_mVect.
auto using lcinf_refl.
Qed.

Lemma labstract_lVect_refl : forall Pi,
  labstract_lVect Pi Pi.
Proof.
intros.
unfold labstract_lVect.
auto using lcinf_refl.
Qed.

Lemma labstract_value_refl : forall al,
  labstract_value al al.
Proof.
intros.
unfold labstract_value.
destruct al.
split.
auto.
intros.
destruct (p ppt). 
auto using labstract_mVect_refl, labstract_lVect_refl.
Qed.


Lemma labstract_value_trans : forall al al' al'',
  labstract_value al al' -> labstract_value al' al'' -> labstract_value al al''.
Proof.
unfold labstract_value.
destruct al; destruct al'; destruct al''.
intros.
destruct H.
destruct H0.
split.
auto.
intros.
assert (In ppt l0) by auto.
generalize (H1 _ H3); intro.
generalize (H2 _ H4);intro.
destruct (p ppt).
destruct (p0 ppt).
destruct (p1 ppt).
destruct H5.
destruct H6.
unfold labstract_mVect in *.
unfold labstract_lVect in *.
eauto using lcinf_trans.
Qed.

Lemma labstract_op_stack_refl: forall Os,
  labstract_op_stack Os Os.
Proof.
induction Os.
constructor.
constructor.
apply labstract_value_refl.
assumption.
Qed.

Lemma labstract_op_stack_trans : forall Os Os' Os'',
  labstract_op_stack Os Os' -> labstract_op_stack Os' Os'' -> labstract_op_stack Os Os''.
Proof.
induction Os.
intros.
inv H; inv H0; constructor.
intros.
inv H; inv H0; constructor.
eapply labstract_value_trans ;eauto.
eapply IHOs;eauto.
Qed.

Lemma labstract_local_refl : forall Gamma,
  labstract_local Gamma Gamma.
Proof.
unfold labstract_local.
auto using labstract_value_refl.
Qed.

Lemma labstract_local_trans : forall Gamma Gamma' Gamma'',
  labstract_local Gamma Gamma' -> labstract_local Gamma' Gamma'' -> labstract_local Gamma Gamma''.
Proof.
unfold labstract_local; eauto using labstract_value_trans.
Qed.

Lemma labstract_frame_refl: forall Fr,
  labstract_frame Fr Fr.
Proof.
unfold labstract_frame.
destruct Fr.
auto using labstract_op_stack_refl, labstract_local_refl.
Qed.

Lemma labstract_frame_trans : forall Fr Fr' Fr'',
  labstract_frame Fr Fr' -> labstract_frame Fr' Fr'' -> labstract_frame Fr Fr''.
Proof.
unfold labstract_frame.
intros.
destruct Fr; destruct Fr'; destruct Fr''.
destruct H; destruct H0.
eauto using labstract_op_stack_trans, labstract_local_trans.
Qed.

(* Properties of kill_frame_ and kill_flow *)

Lemma subtyping_kill_flow_value : forall al m c fl,
  labstract_value al (kill_flow_value m c fl al).
Proof.
intros.
unfold labstract_value.
destruct al.
unfold kill_flow_value.
split.
auto.
intro.
destruct (p ppt).
intro.
unfold kill_flow.
split.
unfold labstract_mVect.
auto using lcinf_refl.
unfold labstract_lVect.
intros.
case (a0 m0 c0 fl0).
apply eq_min.
destruct (eq_mc (m,c) (m0,c0));
  destruct (eq_flow fl fl0);apply lcinf_refl.
Qed.

Lemma subtyping_kill_flow_op_stack : forall Os m c fl,
  labstract_op_stack Os (kill_flow_op_stack m c fl Os).
Proof.
induction Os.
compute; constructor.
intros.
simpl.
constructor.
apply subtyping_kill_flow_value.
apply IHOs.
Qed.

Lemma subtyping_kill_flow_local : forall Gamma m c fl,
  labstract_local Gamma (kill_flow_local m c fl Gamma).
Proof.
intros.
unfold labstract_local.
intro.
unfold kill_flow_local.
apply subtyping_kill_flow_value.
Qed.


Lemma subtyping_kill_flow_frame : forall Fr m c fl,
  labstract_frame Fr (kill_flow_frame m c fl Fr).
Proof.
intros.
unfold labstract_frame.
destruct Fr.
unfold kill_flow_frame.
auto using subtyping_kill_flow_local, subtyping_kill_flow_op_stack.
Qed.

(* subtyping *)

Lemma incr_lVect_diff_m : forall pi m c fl m' c' fl',
  m<>m' ->
  incr_lVect pi m c fl m' c' fl' = pi m' c' fl'.
Proof.
intros.
unfold incr_lVect.
destruct (eq_mc (m',c') (m,c)); intros.
inj e.
elim H; reflexivity.
unfold conv_lVect; rewrite LVect.get_upd2; congruence.
Qed.
Lemma incr_lVect_diff_c : forall pi m c fl m' c' fl',
  c<>c' ->
  incr_lVect pi m c fl m' c' fl' = pi m' c' fl'.
Proof.
intros.
unfold incr_lVect, conv_lVect.
rewrite LVect.get_upd2; congruence.
Qed.

Lemma incr_lVect_diff' : forall pi m c fl m' c' fl',
  (m,c,fl) <> (m',c',fl') ->
  incr_lVect pi m c fl m' c' fl' = pi m' c' fl'.
intros.
unfold incr_lVect, conv_lVect.
rewrite LVect.get_upd2; congruence.
Qed.

Lemma sreduction_value : forall l al al' om pi m c fl,
  location_abs l al om pi ->
  labstract_value (kill_flow_value m c fl al) al' ->
  location_abs l al'  om (incr_lVect pi m c fl).
Proof.
intros.
destruct l.

constructor.

unfold kill_flow_value in H0.
unfold labstract_value in H0.
destruct al as (A,F).
destruct al' as (A',F').
destruct H0.
destruct m0 as [a0 [ m0 i0 c0 om0 pi0]].
inv H.
constructor.

auto.

intros.
unfold kill_flow in H1.
generalize (H1 (m0,i0,c0) H12); clear H1.
intro.
destruct (F (m0,i0,c0)).
destruct (F' (m0,i0,c0)).
inj H.
destruct H1.
generalize (H' _ _ (refl_equal _) m' c' fl0).
intro.
unfold labstract_mVect in H.
generalize (H m' c'); intro.
rewrite H2 in H4.
apply eq_inf in H4.
apply H3 in H4.
destruct H4.
split.
assumption.

intros.
assert ((m,c,fl) <> (m',c',fl0)).
intro.
inj H7.
unfold labstract_lVect in H1.
generalize (H1 m' c' fl0).
intro.
MCcase (m',c') (m',c').
Flcase fl0 fl0.
rewrite H6 in H7.
inversion H7.
intuition.
intuition.

rewrite (incr_lVect_diff' pi _ _ _ _ _ _ H7).
apply H5.

unfold labstract_lVect in H1.
generalize (H1 m' c' fl0).
intro.
rewrite H6 in H8.
apply eq_inf.
destruct (eq_mc (m,c) (m',c')).
destruct (eq_flow fl fl0).
inv H8.
assumption.
assumption.
Qed.

Lemma op_stack_abs_size : forall s Os om pi,
  op_stack_abs s Os om pi ->
  length s = length Os.
Proof.
induction s.
intros.
inv H.
reflexivity.
intros.
inv H.
simpl.
rewrite (IHs _ _ _ H').
reflexivity.
Qed.

Lemma op_stack_abs_app : forall s Os v V om pi,
  op_stack_abs (s++v::nil) (Os++V::nil) om pi ->
  op_stack_abs s Os om pi /\ location_abs v V om pi.
Proof.
induction s; destruct Os; simpl; intros.
inv H; repeat constructor; auto.
inv H.
generalize (op_stack_abs_size _ _ _ _ H').
rewrite app_length; simpl.
intros; apply False_ind; omega.
inv H.
generalize (op_stack_abs_size _ _ _ _ H').
rewrite app_length; simpl.
intros; apply False_ind; omega.
inv H.
elim IHs with (1:=H'); intros.
split; auto.
constructor; auto.
Qed.

Lemma sreduction_op_stack : forall s Os Os' om pi m c fl,
  op_stack_abs s Os  om pi ->
  labstract_op_stack (kill_flow_op_stack m c fl Os) Os' ->
  op_stack_abs s Os' om (incr_lVect pi m c fl).
Proof.
induction s.
intros.
inv H.
inv H0.
constructor.
intros.
inv H.
inv H0.
constructor.
eapply sreduction_value; eauto.
eapply IHs;eauto.
Qed.

Lemma sreduction_local : forall rho Gamma Gamma' om pi m c fl,
  local_abs rho Gamma om pi ->
  labstract_local (kill_flow_local m c fl Gamma) Gamma' ->
  local_abs rho Gamma' om (incr_lVect pi m c fl).
Proof.
unfold local_abs, kill_flow_local.
intros.
unfold labstract_local in H0.
eauto using sreduction_value.
Qed.

(* *)

Lemma subtyping_value : forall l al al' om pi,
  location_abs l al om pi ->
  labstract_value al al' ->
  location_abs l al' om pi.
intros.
unfold labstract_value in H0.
destruct al as (A,F);
destruct al' as (A',F');
destruct l as [ _ | [a [m0 i0 c0 om0 pi0]]]; constructor;
destruct H0;
inv H.
auto.
intros.
generalize (H1 _ H12); clear H1;intro Ha.
destruct (F (m0,i0,c0)).
destruct (F'(m0,i0,c0)); inj H.

destruct Ha.

generalize (H m' c').
intro.
rewrite H2 in H3.
apply eq_inf in H3.
generalize (H' a0 a1 (refl_equal _) m' c' fl H3).
intro.
destruct H4.
split.
assumption.

intro.
apply H5.
apply eq_inf.
rewrite <- H6.
auto.
Qed.



Lemma subtyping_op_stack : forall s Os Os' om pi,
  op_stack_abs s Os om pi ->
  labstract_op_stack Os Os' ->
  op_stack_abs s Os' om pi.
Proof.
induction s.
intros.
inv H; inv H0.
constructor.
intros.
inv H; inv H0.
constructor.
eauto using subtyping_value.
eauto.
Qed.

Lemma subtyping_local : forall rho Gamma Gamma' om pi,
  local_abs rho Gamma om pi ->
  labstract_local Gamma Gamma' ->
  local_abs rho Gamma' om pi.
Proof.
unfold local_abs, labstract_local.
intros.
eauto using subtyping_value.
Qed.

Lemma subtyping_frame : forall fr Fr Fr',
  frame_abs fr Fr ->
  labstract_frame Fr Fr' ->
  frame_abs fr Fr'.
Proof.
unfold frame_abs, abstract_frame.
intros.
destruct fr as [ [[m i c om pi] s ] rho].
destruct Fr.
destruct Fr'.
destruct H.
unfold labstract_frame in H0.
destruct H0.
eauto using subtyping_op_stack, subtyping_local.
Qed.

Ltac apply_mult H l := H l.

Ltac destruct_in := 
  match goal with 
    [ H:(let (Os,Gamma) := _ in _) |- _ ] => clear H end.


Ltac subject_value := 
  eapply subtyping_value;
    [ eapply sreduction_value;eauto|
      apply labstract_value_refl].

Ltac subject_op_stack :=
  eapply subtyping_op_stack;
    [eapply sreduction_op_stack;eauto |
      apply labstract_op_stack_refl].
Ltac subject_local :=
      eapply subtyping_local;
        [eapply sreduction_local;eauto | 
          apply labstract_local_refl].

Ltac kill_intro H1 m i c j Om Gamma:=
  generalize (H1 (m,i,c) 
    (kill_flow_op_stack m c (i,next_line i) Om)
    (kill_flow_local m c (i,next_line i) Gamma)
  );intro.


Lemma subst_inv: forall rho Gamma l al om pi x,
  local_abs rho Gamma om pi ->
  location_abs l al om pi ->
  local_abs (subst rho x l) (asubst Gamma x al) om pi.
Proof.
unfold local_abs.
intros.
assert ((subst rho x l x0= l  /\ asubst Gamma x al x0=al)
  \/ (subst rho x l x0 = rho x0 /\ asubst Gamma  x al x0 = Gamma x0)).
unfold subst.
unfold asubst.
destruct (eq_var x x0);
[left; auto | right; auto].
destruct H1.
destruct H1.
rewrite H1.
rewrite H2.
assumption.
destruct H1.
rewrite H1.
rewrite H2.
apply H.
Qed.

Lemma kill_all : forall A F,
  labstract_value (A,F) (A,diff_counters).
Proof.
intros.
unfold labstract_value.
split.
trivial.
intros.
destruct (F ppt).
unfold diff_counters, labstract_mVect, labstract_lVect.
auto using unknow_max.
Qed.

Lemma safe_kill : forall l A F om pi om' pi',
  location_abs l (A,F) om pi ->
  location_abs l (A,diff_counters) om' pi'.
Proof.
intros.
inv H.
constructor.
constructor.
assumption.
intros.
unfold diff_counters in H.
inj H.
discriminate H0.
Qed.

Lemma cinf_max_eq : 
  forall w w', cinf_max w w' = eq ->
    w=eq /\ w' = eq.
Proof.
intros.
unfold cinf_max in H.
destruct w.
destruct w'.
auto.
discriminate H.
discriminate H.
Qed.
(*
Lemma linvoke_counter : 
  forall l al om pi m' c' m c fl,
    location_abs l al om pi ->
    location_abs l 
    (kill_frame_value m' c' (kill_flow_value m c fl al))
    (incr_mVect om m' c') (incr_lVect pi m c fl).
Proof.
intros.
inv H.
constructor.
simpl.
constructor.
assumption.
intros.
case_eq (F(m0,i,c0)).
intros Om' Pi' Ha.
rewrite Ha in H.
simpl in H.
inj H.
generalize (eq_method_prop m' m'0);
  destruct (eq_method m' m'0);
    intros.
generalize (eq_context_prop c' c'0);
  destruct (eq_context c' c'0);
    intros.
discriminate H1.
subst.
generalize (H'  Om' Pi' Ha m'0 c'0 fl0).
intros.
apply H in H1.
destruct H1.
split.
assert ((m'0,c')<>(m'0,c'0)).
intro.
inj H4.
elim H2;reflexivity.
generalize (incr_mVect_diff om m'0 c' m'0 c'0).
intro.
symmetry.
rewrite H1.
apply H5.
auto.*)


Definition abstract_frame_of_method_args args m c :=
    let Gamma := 
      fun x => 
        match nth_error args  x with 
          | Some al => kill_frame_value m c al
          | None => (nil:list PPT, eq_counters)
        end
        in (nil:list abstract_location,Gamma).



Lemma op_stack_abs_append : forall s s' Os Os' om pi,
  op_stack_abs s Os om pi ->
  op_stack_abs s' Os' om pi ->
  op_stack_abs (s++s') (Os++Os') om pi.
Proof.
induction s.
intros.
inv H.
simpl.
assumption.
intros.
inv H.
simpl.
constructor.
assumption.
apply IHs; auto.
Qed.


Lemma op_stack_abs_append_inv : forall s s' Os om pi,
  op_stack_abs (s++s') Os om pi -> 
  exists Osa, exists Osb,
    Os=Osa++Osb /\
    op_stack_abs s Osa om pi /\
    op_stack_abs s' Osb om pi.
Proof.
induction s.
intros.
exists (nil: list abstract_location).
exists Os.
split.
auto.
split.
constructor.
simpl in H.
auto.

intros.
inv H.
apply IHs in H'.
destruct H' as [Osa' [Osb' [? [? ?]]]].
exists (al::Osa').
exists Osb'.
split.
rewrite H.
auto.
split.
constructor; assumption.
assumption.
Qed.

Lemma kill_flow_op_stack_append : 
  forall Os Os' m c fl,
  kill_flow_op_stack m c fl (Os++Os') =
  (kill_flow_op_stack m c fl Os)++
  (kill_flow_op_stack m c fl Os').
Proof.
induction Os.
intros.
simpl; reflexivity.
intros.
simpl.
rewrite (IHOs).
reflexivity.
Qed.

Lemma split_eq_append : 
  forall A (l1:list A) l2 l1' l2',
    l1++l2=l1'++l2' ->
    length l1 = length l1' ->
    l1=l1' /\ l2=l2'.
Proof.
induction l1.
intros.
destruct l1'.
auto.
discriminate H0.
intros.
destruct l1'.
discriminate H0.
inj H.
simpl in H0.
inj H0.
destruct (IHl1 _ _ _ H1 H).
subst.
auto.
Qed.

Lemma kill_flow_op_stack_size : forall m c fl Os,
  length (kill_flow_op_stack m c fl Os) = length Os.
induction Os.
simpl;reflexivity.
simpl.
rewrite IHOs.
reflexivity.
Qed.

Lemma subtyping_invoke_local : forall Fr Fr' m c,
  labstract_local Fr Fr' ->
  labstract_local (kill_frame_local m c Fr) (kill_frame_local m c Fr').
Proof.
intros.
unfold labstract_local.
intro.
unfold labstract_value.
case_eq (kill_frame_local m c Fr x).
intros A F Ha.
case_eq (kill_frame_local m c Fr' x).
intros A' F' Hb.
generalize (H x).
intro.
unfold labstract_value in H0.
case_eq (Fr x).
intros A0 F0 Hc.
case_eq (Fr' x).
intros A0' F0' Hd.
rewrite Hc in H0.
rewrite Hd in H0.
destruct H0.
unfold kill_frame_local in Ha.
unfold kill_frame_value in Ha.
rewrite Hc in Ha.
unfold kill_frame_local in Hb.
unfold kill_frame_value in Hb.
rewrite Hd in Hb.
inj Ha.
inj Hb.
split.
auto.
intros.
generalize (H1 ppt H2).
intro.
case_eq (F0 ppt).
intros Om Pi He.
case_eq (F0' ppt).
intros Om' Pi' Hf.
rewrite He in H3.
rewrite Hf in H3.
destruct H3.
simpl.
unfold labstract_mVect in *.
unfold labstract_lVect in *.
split.
intros.
destruct eq_mc; intros.
apply lcinf_refl.
apply H3.
intros.
destruct eq_mc; intros.
apply lcinf_refl.
apply H4.
Qed.

Lemma op_stack_abs_nth_error : forall s S om pi,
  op_stack_abs s S om pi -> forall x v,
  nth_error s x = Some v -> 
    exists V, nth_error S x = Some V /\ location_abs v V om pi.
Proof.
  induction 1; simpl.
  destruct x; simpl; intros; try discriminate.
  destruct x; simpl; intros.
  inv H1; eauto.
  eauto.
Qed.

Lemma op_stack_abs_length : forall s S om pi,
  op_stack_abs s S om pi -> length s = length S.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma op_stack_abs_nth : forall s S om pi,
  op_stack_abs s S om pi -> forall n,
  location_abs (nth n s Null) (nth n S (nil, eq_counters)) om pi.
Proof.
  induction 1; simpl; intros.
  destruct n; constructor.
  destruct n; try constructor; auto.
Qed.

Lemma ineq_to_local : forall s S om pi v al,
  location_abs v al om pi ->
  op_stack_abs s S om pi ->
  local_abs (local_of_list v s) (abstract_local_of_list al S) om pi.
Proof.
  intros.
  unfold local_abs, local_of_list, abstract_local_of_list in *.
  intros x.
  destruct x; auto.
  rewrite (op_stack_abs_length _ _ _ _ H0) in *.
  destruct (le_gt_dec (Datatypes.S x) (length S)).
  apply op_stack_abs_nth; auto.
  constructor.
Qed.

Lemma b : forall l al om pi m c omg,
  location_abs l al om pi ->
  location_abs l (kill_frame_value m c al) (invoke_mVect om m c omg) 
  (invoke_lVect pi m c).
Proof.
intros.
destruct l.
constructor.
destruct m0 as [a0 [m0 i0 c0 om0 pi0]].
destruct al as [A F].
inv H.
simpl.
constructor.
assumption.
intros Om' Pi'.
intros.
unfold kill_frame in H.
case_eq (F (m0,i0,c0)).
intros Om Pi Ha.
rewrite Ha in H.
inj H.
unfold invoke_mVect.
destruct eq_mc.
discriminate.
unfold invoke_lVect, incr_lVect, conv_lVect, conv_mVect in *.
rewrite MVect.get_upd2; try congruence.
rewrite LVect.get_clear; try congruence.
simpl.
destruct (eq_mc (m', c') (m, c)).
elim n; auto.
eapply H'; eauto.
Qed.


Lemma cxx : forall rho Gamma om pi m c omg,
  local_abs rho Gamma om pi ->
  local_abs rho (kill_frame_local m c Gamma) (invoke_mVect om m c omg) 
  (invoke_lVect pi m c).
Proof.
intros.
unfold local_abs in *.
intros.
unfold kill_frame_local.
apply b.
auto.
Qed.

Lemma dxx : forall m c fl s s',
  kill_flow_op_stack m c fl (s++s') = (kill_flow_op_stack m c fl s)++
  (kill_flow_op_stack m c fl s').
Proof.
induction s.
intros.
simpl.
reflexivity.
intros.
simpl.
rewrite IHs.
reflexivity.
Qed.

Inductive call_stack_ret : call_stack -> Prop :=
| call_stack_ret_nil : call_stack_ret nil
| call_stack_ret_single : forall fr,
  call_stack_ret (fr::nil)
| call_stack_ret_cons : forall m i c (om om':mVect) (pi pi':lVect) s rho
  m' i' c' s' rho' cs
  (H: forall m'' c'' fl, (m,c) <>(m'',c'') ->
    om' m'' c''= om m'' c'' /\ 
    pi' m'' c'' fl = pi m'' c'' fl)
  (H':call_stack_ret ((CP m' i' c' om' pi',s',rho')::cs)),
  call_stack_ret 
  ((CP m i c om pi,s,rho)::(CP m' i' c' om' pi',s',rho')::cs).

Ltac MLtac l l' :=
    destruct (S.eq_memloc l l'); [subst | idtac].
  
Lemma call_stack_ret_prop :
  forall p L L' sigma sigma' mu mu' omg omg' e,
    (forall l cs, L l=Some cs -> call_stack_ret cs) ->
    step p (L,sigma,mu,omg) (L',sigma',mu',omg') e ->
    (forall l cs, L' l=Some cs -> call_stack_ret cs).
Proof.
intros.
inv H0.
inv H11.
MLtac' o l.
rewrite upd_thread_new in H1.
inj H1.
inv H14.
apply H in H12.
inv H12.
constructor.
destruct fr' as [[[m0 i0 c0 om0 pi0] s0] rho0].
constructor.
intros.
assert ((m,c)=(m0,c0) /\ (om=om0)) by
  (inv H9; auto).
destruct H2.
inj H2.
generalize (H1 _ _ fl H0).
intro.
destruct H2.
split.
assumption.
assert (pi0 = incr_lVect pi m0 c0 (i,i0)) by
  (inv H9;auto).
assert ((m0,c0,(i,i0)) <> (m'',c'',fl)).
intro.
inj H5.
elim H0; reflexivity.
generalize (incr_lVect_diff' pi m0 c0 (i,i0) m'' c'' fl H5).
intro.
rewrite H3.
rewrite <- H6.
rewrite H4.
reflexivity.
assumption.

generalize (H _ _ H12).
clear H12 H.
intro.
constructor.
intros.
split.
unfold invoke_mVect, conv_mVect in *.
rewrite MVect.get_upd2 in *; auto.
unfold invoke_lVect, incr_lVect, conv_lVect in *.
rewrite LVect.get_clear in *; auto.
simpl.
destruct ( eq_mc (m'', c'')
            (m1, C.make_call_context m i c (C.make_new_context m0 i0 cId c0))).
elim H0; auto.
auto.

inv H.
constructor.
constructor.
intros.
assert ((m,c,(i,S i)) <> (m'',c'',fl)).
intro.
inj H0.
elim H; reflexivity.
generalize (incr_lVect_diff' pi m c (i, S i) m'' c'' fl H0).
intro.
rewrite H2.
apply H1.
assumption.
assumption.

generalize (H _ _ H12).
intro.
inv H0.
constructor.
assumption.

generalize (H _ _ H12).
intro.
inv H0.
inv H'.
constructor.
constructor.
apply H1.
apply H'0.
rewrite (upd_thread_old) in H1.
eauto.
assumption.

unfold upd_thread in H1.
simpl in *; Case'.
inj H1.
constructor.
MLtac' o l.
inj H1.
generalize (H _ _ H12).
intro.
inv H0.
constructor.
constructor.
intros.
assert ((m,c,(i,S i)) <> (m'',c'',fl)).
intro.
inj H1.
elim H0; reflexivity.
generalize (incr_lVect_diff' pi m c (i, S i) m'' c'' fl H1).
intro.
rewrite H3.
apply H2.
assumption.
assumption.
eauto.

MLtac' o l.
rewrite upd_thread_new in H1.
inj H1.
generalize (H _ _ H12).
intro.
inv H0.
constructor.
constructor.
intros.
assert ((m,c,(i,S i)) <> (m'',c'',fl)).
intro.
inj H1.
elim H0; reflexivity.
generalize (incr_lVect_diff' pi m c (i, S i) m'' c'' fl H1).
intro.
rewrite H3.
apply H2.
assumption.
assumption.
rewrite (upd_thread_old) in H1; eauto.

MLtac' o l.
rewrite upd_thread_new in H1.
inj H1.
generalize (H _ _ H12).
intro.
inv H0.
constructor.
constructor.
intros.
assert ((m,c,(i,S i)) <> (m'',c'',fl)).
intro.
inj H1.
elim H0; reflexivity.
generalize (incr_lVect_diff' pi m c (i, S i) m'' c'' fl H1).
intro.
rewrite H3.
apply H2.
assumption.
assumption.
rewrite (upd_thread_old) in H1; eauto.
Qed.

Lemma CSRet_reachable : forall p st,
  reachable p st -> forall L sigma omg mu,
  st=(L,sigma,omg,mu) ->
  forall l cs, L l =Some cs -> call_stack_ret cs.
Proof.
induction 1.
intros.
inv H.
unfold threads_init in *.
Case'.
subst.
inj H0.
constructor.
congruence.
intros.
destruct st as [[[L' sigma'] omg'] mu'].
generalize (IHreachable L' sigma' omg' mu' (refl_equal _));intro.
subst.
eapply call_stack_ret_prop;eauto.
Qed.

Lemma CSret_prop : 
  forall v al m i c om pi s rho
    m' i' c' om' pi' s' rho' cs,
  location_abs v al om pi ->
  call_stack_ret 
  ((CP m i c om pi, s,rho)::
    (CP m' i' c' om' pi',s',rho')::cs) ->
  location_abs v 
  (kill_frame_value m c al) om' pi'.
Proof.
intros.
inv H0.
clear H'.
destruct v.
constructor.
destruct m0 as [a0 [m0 i0 c0 om0 pi0]].
destruct al as [A0 F0].
simpl.
inv H.
constructor.
assumption.
intros.
case_eq (F0 (m0,i0,c0)).
intros Om0 Gamma0 Ha.
rewrite Ha in H.
simpl in H.
inj H.
generalize (H' Om0 Gamma0 Ha m'0 c'0 fl).
intro.
destruct eq_mc.
discriminate.
apply H in H0; clear H.
destruct (H2 m'0 c'0 fl n).
split.
intuition congruence.
intros; rewrite H1; intuition.
Qed.

Lemma kill_frame_value_inv : forall al al' m c,
  labstract_value al al' ->
  labstract_value 
  (kill_frame_value m c al)
  (kill_frame_value m c al').
Proof.
intros.
destruct al as [ A F].
destruct al' as [A' F'].
inv H.
constructor.
assumption.
intros.
generalize (H1 _ H).
intro.
case_eq (F ppt).
intros Om Pi Ha.
case_eq (F' ppt).
intros Om' Pi' Hb.
rewrite Ha in H2.
rewrite Hb in H2.
destruct H2.
unfold kill_frame.
unfold labstract_mVect in *.
unfold labstract_lVect in *.
split.
intros.
  destruct (eq_mc (m,c) (m0,c0));intros.
apply lcinf_refl.
apply H2.
intros.
  destruct (eq_mc (m,c) (m0,c0));intros.
apply lcinf_refl.
apply H3.
Qed.


Lemma alloc_new_null : forall sigma l sigma' m f,
  alloc sigma l sigma' -> sigma' l = Some m -> m f = Null.
Proof.
intros.
unfold alloc in H.
destruct H as [? [? ?]].
rewrite H1 in H0.
inj H0.
reflexivity.
Qed.

Section Safety.
  Variable p : program.
  Variable cg : method -> C.mcontext -> Prop.
  Variable M : abstract_signatures.
  Variable Frs : abstract_frames.
  Variable Sigma : abstract_heap.
  Variable wtyped : typing p cg M Frs Sigma.

  Lemma local_step0 : forall l m i j  c om pi s s' rho rho' cs sigma sigma' instr e
    (HCG : cg m c)
    (HDtyping : dynamic_typing ((CP m i c om pi,s,rho)::cs) M Frs)
    (HHeapAbs : heap_abs sigma Sigma)
    (HInstr : m.(body) i = Some instr)
    (HStep : step0 l (m,i,c) instr (i,s,rho,sigma) (j,s',rho',sigma') e),
    dynamic_typing ((CP m j c om (incr_lVect pi m c (i,j)) ,s',rho')::cs) M Frs.
  Proof.
    intros.
    inv HDtyping.
    constructor; [idtac | assumption].
    inv wtyped.
    unfold transfer_cond in H.
    assert (HCFlow:cflow m (i,j)) by 
      (eauto using step0_cflow).
    generalize (H _ _ _ _ _ HCG HCFlow HInstr).
    clear H; intro HTransfer.

      case_eq (Frs (m,i,c)).
    intros Om Gamma Ha.
    rewrite Ha in *.
    case_eq (Frs (m,j,c)).
    intros Om' Gamma' Hb.
    rewrite Hb in *.


    unfold frame_abs in *.
    destruct H9 as [Hc Hd].
    inv HStep; inv HTransfer.
           
    destruct H7 as [He Hf].
    inv He.
    split.
    constructor.
    constructor.
    subject_op_stack.
    subject_local.

    destruct H6 as [He Hf].
    inv He.
    split.
    constructor.
    subject_value.
    subject_op_stack.
    subject_local.

      destruct H6 as [He Hf].
    inv Hc.    
    inj H5.
    split.    
    subject_op_stack.    
    eapply subtyping_local.
    apply subst_inv.
    eapply sreduction_local;eauto.
    apply labstract_local_refl.
    subject_value.
    apply labstract_value_refl;eauto.
    assumption.

    inv Hc.
    inj H5.
    destruct al as (A0,F0).
    inj H7.
    destruct o0 as [a0 [m0 i0 c0 om0 pi0]].
    assert (In (m0,i0,c0) A0) by (inversion H12;auto).    
    case_eq (Sigma (m0,i0,c0) f).
    intros A1 F1 Hc.
    assert (location_abs v (A1,diff_counters) om (incr_lVect pi m c (i,next_line i))).
    inv HYP2.
    unfold heap_abs in HHeapAbs.
    destruct H5.
    generalize (HHeapAbs _ _ _ _ _ _ _ _ _ H5 H7).
    intro.
    rewrite Hc in H8.
    eapply safe_kill;eauto.    
    generalize (H6 (m0,i0,c0) A1 F1 H Hc).
    intro.
    destruct H7 as [He Hf].
    inv He.
    split.
    constructor.
    generalize (subtyping_value v (A1,diff_counters) al' _ _ H5 H11).
    auto.    
    subject_op_stack.
    subject_local.

    inv Hc.
    inv H'.
    inj H5.
    destruct H11 as [He Hf].
    constructor.
    subject_op_stack.
    subject_local.
            
    destruct H6.
    constructor.
    subject_op_stack.
    subject_local.
        
    destruct H6.
    constructor.
    subject_op_stack.
    subject_local.
           
    destruct H6.
    constructor.
    subject_op_stack.
    subject_local.
  Qed.

  Lemma heap_step0 : forall l m i j  c om pi s s' rho rho' cs sigma sigma' instr e
    (HCG : cg m c)
    (HDtyping : dynamic_typing ((CP m i c om pi,s,rho)::cs) M Frs)
    (HHeapAbs : heap_abs sigma Sigma)
    (HInstr : m.(body) i = Some instr)
    (HStep : step0 l (m,i,c) instr (i,s,rho,sigma) (j,s',rho',sigma') e),
    heap_abs sigma' Sigma.
  Proof.
    intros.      
    inv HStep; try (assumption).
    
    unfold heap_abs; intros.
    
    destruct (excluded_middle ((o0,f)=((a,CP m0 i0 c0 om0 pi0),f0))).
    inj H1.
    subst.
    assert (w f0=v).
    generalize (write_eq _ _ _ _ _ HYP2).
    intro.
    unfold read in H0.
    destruct H0 as [ ? [? ?]]. 
    rewrite H in H0.
    inj H0.
    reflexivity.
    subst.
    
    inv HDtyping.
    case_eq (w f0).
    intro.
    constructor.
    destruct m1 as [a1 [m1 i1 c1 om1 pi1]].
    intro.
    rewrite H0 in *.
    
    case_eq (Frs (m,i,c)).
    intros Os Gamma Ha.
    rewrite Ha in H10.
    destruct H10.
    inv H1.
    inv H'.
    destruct al as [A1 F1].
    destruct al0 as [A0 F0].

    assert (HCFlow:cflow m (i,next_line i)) by
      (eapply cflow_putfield; eauto).
    inv wtyped.
    unfold transfer_cond in H3.
    
    generalize (H1 _ _ _ _ _ HCG HCFlow HInstr).
    intro.
    rewrite Ha in H10.
    inv H10.
    assert (In (m0,i0,c0) A0) by (inversion H7; auto).
    generalize (H15 (m0,i0,c0) H10).
    intro.
    case_eq (F0 (m0,i0,c0)).
    intros Om0 Pi0 Hu.
    case_eq (Sigma (m0,i0,c0) f0).
    intros A1' F1' Hv.
    rewrite Hu in *.
    rewrite Hv in *.
    simpl in H12.
    destruct H12.
    assert (In (m1,i1,c1) A1) by (inversion H8; auto).
    constructor.    
    apply H12.
    assumption.
    intros.    
    generalize (H13 (m1,i1,c1) H14); intro.
    rewrite H16 in H18.
    destruct H18.
    unfold labstract_mVect in H18.
    generalize (H18 m'  c'); intro.
    case_eq (F1 (m1,i1,c1)).
    intros Om1 Pi1 Hw.
    rewrite Hw in H22.
    simpl in H22.
    rewrite H17 in H22.
    apply eq_inf in H22.
    apply cinf_max_eq in H22.
    destruct H22.
    inv H7.
    inv H8.

      generalize (H'1 _ _ Hw m' c' fl).
    generalize (H' _ _ Hu m' c' fl).
    intros.
    apply H8 in H22.
    apply H7 in H23.
    destruct H22.
    destruct H23.
    split.
    omega.
    
    intro.
    unfold labstract_lVect in H21.
    generalize (H21 m' c' fl);intro.
    rewrite Hw in H27.
    simpl in H27.
    rewrite H26 in H27.
    apply eq_inf in H27.
    apply cinf_max_eq in H27.
    destruct H27.

    destruct (eq_mc (m,c) (m',c'));
        destruct fl;
          destruct (eq_flow (i,next_line i) (l0,l1));
              (discriminate || eauto with arith).
    apply H24 in H27; apply H25 in H28; omega.
    apply H24 in H27; apply H25 in H28; omega.
    apply H24 in H27; apply H25 in H28; omega.

    unfold heap_abs in HHeapAbs.
    generalize (write_diff o0 f (a,CP m0 i0 c0 om0 pi0) f0 sigma sigma' w v H1 HYP2 H).
    intro.
    destruct H2 as [? [? ?]].
    rewrite H0 in H3.
    eapply HHeapAbs; eauto.
  Qed.

  
  Lemma local_step1 : forall l m i j  c om pi pi' s s' rho rho' cs sigma sigma' e
    (HCG : cg m c)
    (HDtyping : dynamic_typing ((CP m i c om pi,s,rho)::cs) M Frs)
    (HHeapAbs : heap_abs sigma Sigma)
    (HStep : step1 l ((CP m i c om pi,s,rho),sigma)
      ((CP m j c om pi',s',rho'),sigma') e),
    dynamic_typing ((CP m j c om pi' ,s',rho')::cs) M Frs.
  Proof.

    intros.
    inv HStep.
    eapply local_step0;eauto.
    inv HDtyping.
    constructor; [idtac | auto].
    assert (cflow m (i,next_line i)) by (eapply cflow_new; eauto).
    inv wtyped.
    unfold transfer_cond in H0.
    generalize (H0 _ _ _ _ (New cid) HCG H HYP1).
    intro.
    case_eq (Frs (m,i,c)).
    intros.
    rewrite H7 in *.
    inv H6.
    inv H9.
    destruct H12.
    split;[ idtac | subject_local].
    
    assert (location_abs (Loc (a, CP m i c om pi)) 
      ((m,i,c)::nil,fresh_counter (m,i,c)) om (incr_lVect pi m c (i,next_line i))).
    constructor.
    apply in_eq.
    intros.
    split.
    reflexivity.
    intro.
    inv H12.

    destruct (eq_ppt (m,i,c) (m,i,c)).
    inj H17.

    destruct (eq_mc (m,c) (m',c')).
    destruct (eq_flow (i,next_line i) fl); try discriminate.

    symmetry.
    apply incr_lVect_diff'; auto.
    congruence.

    symmetry.
    apply incr_lVect_diff'; auto.
    congruence.
    intuition.
   
    inv H9.
    constructor; [idtac | subject_op_stack].
    eapply subtyping_value;eauto.
Qed.

Lemma heap_step1 : forall l m i j  c om pi pi' s s' rho rho' cs sigma sigma' e
  (HCG : cg m c)
  (HDtyping : dynamic_typing ((CP m i c om pi,s,rho)::cs) M Frs)
  (HHeapAbs : heap_abs sigma Sigma)
  (HStep : step1 l ((CP m i c om pi,s,rho),sigma)
    ((CP m j c om pi',s',rho'),sigma') e),
  heap_abs sigma' Sigma.
Proof.
intros.
inv HStep.
eapply heap_step0;eauto.
unfold heap_abs.
intros.
destruct v.
constructor.
assert ((a,CP m i c om pi)<>
  (a0,CP m0 i0 c0 om0 pi0)).
intro.
rewrite <- H1 in H.
generalize (alloc_new_null sigma (a,CP m i c om pi) sigma' w f HYP5 H).
intro.
rewrite H0 in H2.
discriminate H2.
unfold alloc in HYP5.
destruct HYP5.
destruct H3.
generalize (H4 (a0,CP m0 i0 c0 om0 pi0) H1).
intros.
unfold heap_abs in HHeapAbs.
rewrite H5 in H.
eapply HHeapAbs; eauto.
Qed.

Lemma map_kill_flow_op_stack : forall m c fl S1 S2,
  kill_flow_op_stack m c fl (S1++S2) =
  (kill_flow_op_stack m c fl S1)++(kill_flow_op_stack m c fl S2).
Proof.
  induction S1; simpl; auto.
  intros.
  rewrite IHS1; auto.
Qed.

Lemma local_step2 : forall l cs cs' sigma sigma' omg omg' e
  (HCG : forall m i c om pi s rho, 
    In (CP m i c om pi, s,rho) cs -> cg m c)
  (HCSRet : call_stack_ret cs)
  (HDtyping : dynamic_typing cs M Frs)
  (HHeapAbs : heap_abs sigma Sigma)
  (HStep : step2 p l (cs,sigma,omg) (cs',sigma',omg') e),
  dynamic_typing cs' M Frs.
Proof.
intros.
inv HStep.

destruct fr as [[[m i c om pi] s] rho].
destruct fr' as [[[m' i' c' om' pi'] s'] rho'].
assert (m=m'/\ c=c'/\om=om') by (inversion H7;auto).
destruct H as [? [? ?]]; subst.
eapply local_step1; eauto using in_eq.

generalize (HCG _ _ _ _ _ _ _ (in_eq _ _));  clear HCG; intro HCG.
assert (HCFlow:cflow m (i,next_line i)) by (eapply cflow_invoke;eauto).

inv wtyped.
unfold transfer_cond in H.
generalize (H _ _ _ _ _ HCG HCFlow H6).
clear H.
intro transfer_cond'.

inv HDtyping.
case_eq (Frs (m,i,c)).
intros Os Gamma Ha.
case_eq (Frs (m,next_line i,c)).
intros Os' Gamma' Hb.
set (z:=0:line).
case_eq (Frs (m1,z,(C.make_call_context m i c (C.make_new_context m0 i0 cId c0)))).
intros Os0 Gamma0 Hc.
unfold line in *.
rewrite Ha in *.
rewrite Hb in *.
(* params *)
unfold frame_abs in H17.
destruct H17.
apply op_stack_abs_append_inv in H.
destruct H as [Osa [Osb [? [? ?]]]].
inv H9.
rename H15 into Hthis.
destruct al as [A0 F0].

assert (op_stack_abs ((Loc (a0, CP m0 i0 c0 om0 pi0))::nil) ((A0,F0)::nil) om pi) by
  (constructor; [assumption|constructor]).
generalize (op_stack_abs_append _ _ _ _ _ _ H7 H).
intro Hparams.

inv transfer_cond'.
rewrite kill_flow_op_stack_append in H10.
assert (length v_list0 = length (kill_flow_op_stack m c (i,next_line i) Osa)).
rewrite H13.
simpl.
rewrite <- H16.
rewrite kill_flow_op_stack_size.
eapply op_stack_abs_size; eauto.
generalize (split_eq_append _ _ _ _ _ H10 H9).
clear H10 H9.
intro.
destruct H9.
inj H10.


assert (In (m0,i0,c0) A0)by (inversion Hthis ; assumption).


case_eq (M m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0))).
intros (this,fparams) frtype Hd.
unfold invoke_cond in H0.
generalize (H0 m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0)) this fparams frtype Hd).
clear H0.
intro.
change 0 with z in H0.
rewrite Hc in H0.
destruct H0.
inv H0.
generalize (H15 m0 i0 c0 m1 fparams frtype cId this H9 C0 H8 Hd).
clear H15.
intros.
destruct H0.

constructor.
unfold frame_abs.
unfold line in *.
rewrite Hc.
split.
constructor.

generalize (sreduction_op_stack (v_list++(Loc (a0,CP m0 i0 c0 om0 pi0))::nil)
  (Osa++(A0,F0)::nil)
  (kill_flow_op_stack m c (i,next_line i) (Osa++(A0,F0)::nil))
  om pi m c (i,next_line i) Hparams (labstract_op_stack_refl _ )).
clear Hparams.
intro Hparams.
rewrite map_kill_flow_op_stack in *.
simpl in *.
elim op_stack_abs_app with (1:=Hparams).
intros.
generalize (ineq_to_local _ _ _ _ _ _ H14 H12).
clear Hparams; intros  Hparams.

apply subtyping_invoke_local with (m:=m1) (c:=(C.make_call_context m i c (C.make_new_context m0 i0 cId c0))) in H0.
generalize (labstract_local_trans _ _ _ H0 H10).
intro.
apply cxx with (m:=m1) (c:=(C.make_call_context m i c (C.make_new_context m0 i0 cId c0))) (omg:=omg) in Hparams.

simpl in Hparams.
generalize (subtyping_local 
  (local_of_list (Loc(a0,CP m0 i0 c0 om0 pi0)) v_list)  _ _ _ _ Hparams H15).
intro.
assumption.

(* retour *)
destruct frtype.
rewrite Hd.
simpl.
constructor.
intros.
unfold line in *.
change (Datatypes.S i) with (next_line i) in H12.
rewrite Hb in *.
inj H12.
inv H11.
inv H12.
exists al'.
exists Os'.
split.
reflexivity.
split.
assumption.
unfold frame_abs.

split.
eapply sreduction_op_stack;eauto.
eapply sreduction_local; eauto.
assumption.

rewrite Hd.
simpl.
constructor.
constructor.
unfold line in *.
change (Datatypes.S i) with (next_line i).
rewrite Hb.
inv H11.
unfold frame_abs.
split.
eapply sreduction_op_stack; eauto.
eapply sreduction_local;eauto.
auto.

(* return *)
inv HDtyping.
case_eq (M m c).
intros (this,args) rtype Hu.
inversion wtyped.
unfold invoke_cond in H0.
generalize (H0 m c this args rtype Hu).
intro.
unfold return_cond in H1.
generalize (H1 m c (this, args) rtype Hu i H7).
intro.
rewrite Hu in H11.
rewrite H14 in H11.
simpl in H11.
inv H11.
assumption.
(* Areturn *)

inv HDtyping.
case_eq (M m c).
intros args rtype Hu.
inv wtyped.
unfold areturn_cond in H2.
generalize (H2 m c args rtype Hu).
intro.
generalize (H5 i H7); intros.
destruct H6 as [al' [? ?]].
rewrite H6 in Hu.
rewrite Hu in H11.
inv H11.
clear H0.
case_eq (Frs (m,i,c)).
intros Os Gamma Hw.
generalize (H8 Os Gamma Hw). 
intro.
destruct H0 as [al [Os' [? ?]]].
rewrite H0 in Hw.
case_eq (Frs (m0,i0,c0)).
intros Os0 Gamma0 Hv.
generalize (H20 Os0 Gamma0 Hv).
intro.
destruct H9 as [al'0 [ Os'0 [? [? ?]]]].

constructor.
rewrite Hv.
rewrite H9.
unfold frame_abs in H12 |-*.
destruct H12.
split.

constructor.

assert (location_abs v al om pi).
unfold line in *.
rewrite Hw in H10.
unfold frame_abs in H10.
destruct H10.
inv H10.
assumption.

assert (location_abs v (kill_frame_value m c al) om0 pi0).
eapply CSret_prop.
apply H14.
apply HCSRet.
eapply subtyping_value.
apply H15.
assert (labstract_value 
  (kill_frame_value m c al) 
  (kill_frame_value m c al')).
apply kill_frame_value_inv;auto.
eapply labstract_value_trans;eauto.
auto.
auto.
auto.
Qed.

Lemma heap_step2 : forall l cs cs' sigma sigma' omg omg' e
  (HCG : forall m i c om pi s rho, 
    In (CP m i c om pi, s,rho) cs -> cg m c)
  (HCSRet : call_stack_ret cs)
  (HDtyping : dynamic_typing cs M Frs)
  (HHeapAbs : heap_abs sigma Sigma)
  (HStep : step2 p l (cs,sigma,omg) (cs',sigma',omg') e),
  heap_abs sigma' Sigma.
Proof.
intros.
inv HStep; (try assumption).
destruct fr as [[[m i c om pi] s]rho].
destruct fr' as [[[m' i' c' om' pi'] s']rho'].
assert ((m,c,om)=(m',c',om')) by
  (inv H7;reflexivity).
inj H.
eapply heap_step1; eauto using in_eq.
Qed.

Lemma local_step : forall L mu omg L' sigma sigma' mu' omg' e
  (HCG : forall l cs, L l = Some cs ->
    forall m i c om pi s rho,
      In (CP m i c om pi, s,rho) cs -> cg m c)
  (HCSRet : forall l cs, L l=Some cs ->call_stack_ret cs)
  (HDtyping : forall l cs, L l = Some cs -> dynamic_typing cs M Frs)
  (HHeapAbs : heap_abs sigma Sigma)
  (HStep : step p (L,sigma,mu,omg) (L',sigma',mu',omg') e),  
  forall l cs, L' l = Some cs -> 
    dynamic_typing cs M Frs.
Proof.
intros.
inv HStep.

MLtac' o l.

generalize (HCG l (fr::cs0) H10).
generalize (HCSRet l (fr::cs0) H10).
generalize (HDtyping l (fr::cs0) H10).
clear HCG HCSRet HDtyping.
intros HDtyping HCSRet HCG.

inv H9.
rewrite upd_thread_new in H.
inv H.
eapply local_step2; eauto.

inv HDtyping.
unfold upd_thread in *.
simpl in *; Case'.
rewrite H22 in H10.
discriminate.
MLtac' l l.
inv H.
constructor;[idtac | assumption].
inv wtyped.
unfold transfer_cond in H.

generalize (HCG m i c om pi (Loc (a0, CP m0 i0 c0 om0 pi0)::s') rho (in_eq _ _)).
clear HCG.
intro HCG.
assert (cflow m (i, next_line i)) by
  (apply cflow_start; auto).
generalize (H m c i (next_line i) Run HCG H5 H13).
intro transfer_cond'.
case_eq (Frs (m,i,c)).
intros Os Gamma Ha.
case_eq (Frs (m,next_line i,c)).
intros Os' Gamma' Hb.
unfold line in *.
rewrite Ha in *.
rewrite Hb in *.
inv transfer_cond'.
unfold frame_abs in H11.
destruct H11.
destruct Os.
simpl in *.
discriminate.
simpl in *.
inj H6.
inv H7.
destruct a as [A F].
simpl in *.
inj H14.

assert (In (m0,i0,c0) A) by
  (inversion H20;auto).
case_eq (M m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0))).
intros (fthis,fparams) frtype Hu.
generalize (H9 m0 i0 c0 m1 fparams frtype cId fthis H6 C0 H16 Hu).
clear H9.
intro H9.
destruct H9.
destruct H9.
split.
eapply sreduction_op_stack; eauto.
eapply sreduction_local; eauto.
intuition.

unfold upd_thread in *.
inv HDtyping.
MLtac' l l; [idtac|intuition].
inv H.
constructor.
unfold frame_abs in H11.
case_eq (Frs (m,i,c)).
intros Os Gamma Ha.
case_eq (Frs (m,next_line i,c)).
intros Os' Gamma' Hb.
unfold line in *.
rewrite Ha in H11.
destruct H11.
generalize (HCG _ _ _ _ _ _ _ (in_eq _ _)).
intro.
assert (cflow m (i,S i)) by
  (apply cflow_monitorenter; auto).
inv wtyped.
unfold transfer_cond in H3.
generalize  (H3 m c i (S i) MonitorEnter H1 H2 H14).
intro.
unfold line in *.
rewrite Ha in H9.
change (S i) with (next_line i) in H9.
rewrite Hb in H9.
inv H9.
unfold labstract_frame in H17.
destruct H17.
destruct Os.
simpl in H11.
discriminate H11.
simpl in H11.
inj H11.
split.
inv H.
eapply sreduction_op_stack; eauto.
eapply sreduction_local; eauto.
assumption.

unfold upd_thread in *.
MLtac' l l; [idtac|intuition].
inv HDtyping.
inv H.
constructor.
unfold frame_abs in H11.
case_eq (Frs (m,i,c)).
intros Os Gamma Ha.
case_eq (Frs (m,next_line i,c)).
intros Os' Gamma' Hb.
unfold line in *.
rewrite Ha in H11.
destruct H11.
generalize (HCG _ _ _ _ _ _ _ (in_eq _ _)).
intro.
assert (cflow m (i,S i)) by
  (apply cflow_exit; auto).
inv wtyped.
unfold transfer_cond in H3.
generalize  (H3 m c i (S i) MonitorExit H1 H2 H14).
intro.
unfold line in *.
rewrite Ha in H9.
change (S i) with (next_line i) in H9.
rewrite Hb in H9.
inv H9.
unfold labstract_frame in H17.
destruct H17.
destruct Os.
simpl in H11.
discriminate H11.
simpl in H11.
inj H11.
split.
inv H.
eapply sreduction_op_stack; eauto.
eapply sreduction_local; eauto.
assumption.

inv H9.
(* step2 *)
unfold upd_thread in *.
MLtac' o l; [intuition|idtac].
eauto.

(* run *)
unfold upd_thread in *.
MLtac' o l; [intuition|idtac].
simpl in *; Case'.
inv H.
assert (signature m1 = run) by
  (destruct (lookup_prop_1 _ _ _ _ H16) as [?[? [? [? ?]]] ]; auto).

case_eq (M m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0))).
intros ((A,F),fparams) frtype Ha.

inv wtyped.
unfold transfer_cond in H0.
assert (HCFlow:cflow m (i, S i)) by
  (apply cflow_start;auto).
generalize (HCG _ _ H10 _ _ _ _ _ _ _ (in_eq _ _)).
clear HCG; intro HCG.
generalize (H0 _ _ _ _ _ HCG HCFlow H13).
intro.
unfold start_cond in H4.
generalize (H4 m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0)) fparams frtype A F H Ha).
intro.
generalize (HDtyping  _ _ H10).
intro.
inv H8.
case_eq (Frs (m,i,c)).
intros Os Gamma Hb.
case_eq (Frs (m,S i,c)).
intros Os' Gamma' Hc.
unfold line in *.
rewrite Hb in *.
rewrite Hc in *.
unfold frame_abs in H23.
destruct H23.
inv H8.
destruct al as [A' F'].
assert (In (m0,i0,c0) A') by (inversion H18;auto).
inv H6.
generalize (H14 _ _ _ _ _ _ _ _ H8 C0 H16 Ha).
clear H14.
intro.
destruct H7.
(*destruct H11 as [A0 [ F0 [?[? ?]]]].*)
(*rewrite H6 in H8.*)

constructor.
unfold frame_abs.
set (z:=0:line) in *.
case_eq (Frs (m1,z,C.make_call_context m i c (C.make_new_context m0 i0 cId c0))).
intros Os1 Gamma1 Hu.
unfold line in *.
rewrite Hu in H11.
unfold labstract_frame in H11.
destruct H11.
inv H11.
split.
constructor.
eapply subtyping_local 
  with (Gamma:=abstract_local_of_list (A,diff_counters) nil).
unfold local_abs.
intro.
case x.
unfold local_of_list, abstract_local_of_list.
simpl.
unfold labstract_local in H8.
generalize (H9 0).
intro.
unfold local_of_list, abstract_local_of_list in *.
simpl in *.
constructor.
destruct H6.
generalize (H6 0).
intros.
destruct H14.
eauto.
intros.
case_eq (diff_counters (m0,i0,c0)).
intros.
unfold diff_counters in H15.
inj H15.
unfold diff_counters in H11.
inj H11.
discriminate.
intro.
unfold local_of_list, abstract_local_of_list.
simpl.
constructor.
unfold abstract_local_of_list.
apply H12.
rewrite Ha.
simpl.
rewrite H7.
constructor.
constructor.

eapply HDtyping; eauto.

unfold upd_thread in *.
MLtac' o l; [intuition|idtac].
eapply HDtyping; eauto.

unfold upd_thread in *.
MLtac' o l; [intuition|idtac].
eapply HDtyping; eauto.
Qed.

Lemma heap_step : forall L mu omg L' sigma sigma' mu' omg' e
  (HCG : forall l cs, L l = Some cs ->
    forall m i c om pi s rho,
      In (CP m i c om pi, s,rho) cs -> cg m c)
  (HCSRet : forall l cs, L l=Some cs ->call_stack_ret cs)
  (HDtyping : forall l cs, L l = Some cs -> dynamic_typing cs M Frs)
  (HHeapAbs : heap_abs sigma Sigma)
  (HStep : step p (L,sigma,mu,omg) (L',sigma',mu',omg') e),  
  heap_abs sigma' Sigma.
Proof.
intros.
inv HStep.
inv H8;try assumption.
eapply heap_step2;eauto.
Qed.
End Safety.

Definition SafeCG (p:program) (cg:method->C.mcontext->Prop) : Prop :=
    forall sigma omg mu L cs l,
      reachable p (L,sigma,omg,mu) ->
      L l =Some cs ->
      forall m i c om pi s rho,
        In (CP m i c om pi, s, rho) cs -> 
        cg m c.

Lemma heap_abs_result_aux : forall p st,
  reachable p st -> forall cg,
  SafeCG p cg ->
  forall M Frs Sigma,
    typing p cg M Frs Sigma ->
    forall L sigma omg mu,       
      st=(L,sigma,omg,mu) ->
      (forall l cs, L l = Some cs -> 
        dynamic_typing cs M Frs)
      /\ heap_abs sigma Sigma.
Proof.
induction 1.
intros cg Hcg M Frs Sigma H L sigma omg mu H0.
unfold init in H0.
inj H0.
split.
intros.
unfold threads_init in H0.
Case'.
inj H0.
unfold cp_init.
constructor.
unfold frame_abs.
unfold line in *.
case_eq (Frs (main p, 0, C.init_mcontext)).
intros Os Gamma Ha.
unfold main in.
inv H.
unfold main_cond in H5.
destruct H5.
rewrite Ha in H5.
destruct H5.
split.
inv H5.
constructor.
eapply subtyping_local.
2:apply H6.
unfold local_abs.
intro.
destruct x.
unfold run_address, cp_run_address.
constructor.
constructor.
simpl.
inv H.
inv H5.
rewrite H.
constructor.
constructor.
discriminate H0.
unfold sigma_init.
unfold heap_abs.
intros.
destruct (eq_memloc (a,CP m i c om pi) (run_address, cp_run_address p)).
inj H0.
constructor.
discriminate H0.

(* induction *)
intros.
destruct st as [[[L0 sigma0] omg0]mu0].
subst.
assert (Hcg:=H0 sigma0 omg0 mu0).
generalize (IHreachable cg H0 M Frs Sigma H1 L0 sigma0 omg0 mu0 (refl_equal _)).
intro.
destruct H2.
inv H1.
split.
intros.

eapply local_step with (6:=H'); eauto.
constructor; eauto.
intros.
eapply Hcg; eauto.
intros.
generalize (CSRet_reachable _ _ H _ _ _ _ (refl_equal _)).
intro.
eapply H11; eauto.

eapply heap_step with (6:=H'); eauto.
constructor; eauto.
intros.
eapply Hcg; eauto.
generalize (CSRet_reachable _ _ H _ _ _ _ (refl_equal _)).
eauto.
Qed.

Lemma heap_abs_result : forall p cg,
  SafeCG p cg -> 
  forall M Frs Sigma,
    typing p cg M Frs Sigma ->
    forall L sigma omg mu,     
      reachable p (L,sigma,omg,mu) -> 
      heap_abs sigma Sigma.
Proof.
intros.
generalize (heap_abs_result_aux _ _ H1 _ H _ _ _ H0).
intro.
destruct (H2 _ _ _ _ (refl_equal _)); auto.
Qed.



End TypeSafety.









  


