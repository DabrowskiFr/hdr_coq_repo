Require Export counting_semantic.

Module DomainProp (Import S:COUNTING_SEMANTIC). 


Lemma incr_mVect_lt : 
 forall (om:mVect) m c m' c',
  om m c <= incr_mVect om m' c' m c.
Proof.
unfold conv_mVect; intros.
unfold incr_mVect.
destruct (eq_mc (m,c) (m',c')).
inv e; rewrite MVect.get_upd1; auto with arith.
rewrite MVect.get_upd2; auto with arith.
Qed.

Lemma incr_lVect_lt :
  forall (pi:lVect) m m' c c' fl i j,
    pi m c fl <= (incr_lVect pi m' c' (i,j)) m c fl.
Proof.
  unfold conv_lVect; intros.
  unfold incr_lVect.
  destruct (Domain_lVect.eq_domain (m,c,fl) (m',c',(i,j))).
  inv e; rewrite LVect.get_upd1; auto with arith.
  rewrite LVect.get_upd2; auto with arith.
Qed.

Lemma incr_pi_prop2 : 
  forall m c fl fl' pi pi',
    pi'=incr_lVect pi m c fl -> fl<>fl' -> (pi' m c fl') = (pi m c fl').
Proof.
  unfold conv_lVect; intros.
  rewrite H.
  unfold incr_lVect.
  rewrite LVect.get_upd2; auto with arith.
  congruence.
Qed. 

Lemma subst_eq : forall l x v, subst l x v x = v.
Proof.
intros.
unfold subst.
comp x x; intuition.
Qed.


Lemma subst_diff : forall l x y v, x<>y -> subst l x v y = l y.
Proof.
intros.
unfold subst.
comp x y; intuition.
Qed.

Lemma subst_p2p : forall (P:val -> Prop) (rho:local) (v:val),
  forall x v, 
    (forall y, P (rho y)) -> P v -> (forall y, P ((subst rho x v) y)).
Proof.
intros.
unfold subst.
comp x y; intuition.
Qed.

Lemma subst_coDom :
  forall rho x y v v',
  (subst rho x v) y = v' -> v'=v \/ rho y = v'.
Proof.
intros.
unfold subst in *.
comp x y; intuition.
Qed.

Lemma op_stack_push : forall (P:val->Prop) (s:op_stack) (v:val), 
  (forall v', In v' s -> P v') -> P v -> (forall v', In v' (v::s) -> P v').
Proof.
  intros.
  apply in_inv in H1.
  destruct H1.
  rewrite <- H1.
  assumption.
  apply H.
  assumption.
Qed.

Lemma op_stack_pop1 : forall (P:val -> Prop) (s:op_stack) (v:val),
  (forall v' , In v' (v::s) -> P v') -> P v.
Proof.
  intros.
  apply H.
  unfold In.
  left.
  reflexivity.
Qed.

Lemma op_stack_pop2 : forall (P:val -> Prop) (s:op_stack) (v:val),
  (forall v', In v' (v::s) -> P v') -> (forall v', In v' s -> P v').
Proof.
intros.
apply H.
apply in_cons.
assumption.
Qed.


(* Properties of inDom *)
(**********************************************************)

(* Properties of alloc *)
Lemma inDom_New :   forall sigma l sigma',
    alloc sigma l sigma' -> inDom l sigma'.
Proof.
unfold alloc, inDom.
intros.
destruct H as [_ [Ha _]].
rewrite Ha.
discriminate.
Qed.

Lemma new_dom_sub :
  forall l l' sigma sigma',
  inDom l sigma -> alloc sigma l' sigma' -> inDom l sigma'.
Proof.
unfold inDom, alloc.
intros.
destruct H0 as [_ [Ha Hb]].
destruct (excluded_middle (l'=l)).
subst; rewrite Ha; discriminate.
rewrite (Hb l H0);auto.
Qed.

Lemma alloc_coDom :
  forall sigma sigma' l l',
  alloc sigma l sigma' -> inDom  l' sigma' -> (l'=l \/ inDom l' sigma).
Proof.
unfold alloc, inDom.
intros.
destruct (excluded_middle (l=l')).
auto.
destruct H as [_ [_ Hb]].
right; intros.
rewrite <- (Hb l' H1).
assumption.
Qed.


(* Properties of read *)
(**********************************************************)
Lemma read_injective :
  forall sigma l f v v',
    read sigma l f v -> read sigma l f v' -> v=v'.
Proof.
unfold read.
intros.
destruct H as [m [Ha Hb]].
destruct H0 as [m' [Hc Hd]].
subst.
rewrite Ha in Hc.
injection Hc;intro;subst.
reflexivity.
Qed.

(* Properties of setfield *)
(**********************************************************)
Lemma updateField_eq :
  forall (m:field->val) (f:field) (v:val), 
    updateField m f v f = v.
Proof.
intros; unfold updateField.
comp f f; intuition.
Qed.

Lemma updateField_diff :
  forall (m:field -> val) (f:field) (v:val) (f':field), 
    f<>f' -> updateField m f v f' = m f'.
Proof.
intros; unfold updateField.
comp f f'; intuition.
Qed.

(* Properties of write *)
(**********************************************************)

Lemma write_dom_eq : forall sigma l l' f v sigma',
  write sigma l f v sigma' -> (inDom l' sigma -> inDom l' sigma').
Proof.
unfold inDom.
intros.
unfold write in H.
destruct H as [[Ha [Hb Hc]] Hd].
destruct (excluded_middle (l=l'));
  [subst; rewrite Hc; discriminate | rewrite (Hd l' H); assumption].
Qed.

Lemma write_dom_eq_inv : forall sigma l l' f v sigma',
  write sigma l f v sigma' -> (inDom l' sigma' -> inDom l' sigma).
Proof.
unfold inDom, write.
intros.
destruct H as [[Ha [Hb Hc]] Hd].
destruct (excluded_middle (l=l'));
  [subst; rewrite Hb; discriminate | rewrite <- (Hd l' H); assumption].
Qed.


Lemma write_eq : 
  forall sigma l f v sigma',
    (write sigma l f v sigma') -> (read sigma' l f v).
Proof.
unfold read, write.
intros.
destruct H as [[Ha [Hb Hc]] Hd].
exists (updateField Ha f v).
split; [assumption | apply updateField_eq].
Qed.

Lemma write_diff_field :
  forall sigma l f f' v v' sigma', 
    write sigma l f v sigma' -> f <> f' -> 
    read sigma l f' v' -> read sigma' l f' v'.
Proof.
unfold read, write.
intros.
destruct H as [[m [Ha Hb]] Hc]. 
exists (updateField m f v).
split;
  [assumption |
    destruct H1 as [m' [Hd He]];
      subst; rewrite Ha in Hd;
          injection Hd; intros; subst;
            apply updateField_diff; assumption].
Qed.

Lemma write_diff_field_inv :
  forall sigma l f f' v v' sigma', 
    write sigma l f v sigma' -> f <> f' -> 
    read sigma' l f' v' -> read sigma l f' v'.
Proof.
unfold read, write.
intros.
destruct H as [[m [Ha Hb]]].
destruct H1 as [m' [Hc Hd]].
exists m.
split; 
  [ assumption |
    subst; rewrite Hb in Hc;
      injection Hc; intros; subst;
        symmetry; apply updateField_diff; assumption].
Qed.

Lemma write_diff_loc : forall sigma l f f' v sigma' l' v',
  write sigma l f v sigma' -> l<>l' -> 
  (read sigma l' f' v' -> read sigma' l' f' v').
Proof.
unfold read, write.
intros.
destruct H as [[m [Hb Hc]]Hd].
destruct H1 as [m' [Hf Hg]].
exists m'.
rewrite <- (Hd l' H0) in Hf.
split;assumption.
Qed.

Lemma write_diff_loc_inv : forall sigma l f f' v sigma' l' v',
  write sigma l f v sigma' -> l<>l' -> 
  (read sigma' l' f' v' -> read sigma l' f' v').
Proof.
unfold read, write.
intros.
destruct H as [[m [Hb Hc]]Hd].
destruct H1 as [m' [Hf Hg]].
exists m'.
rewrite (Hd l' H0) in Hf.
split;assumption.
Qed.

Lemma write_p2p : forall (P:val -> Prop) (sigma sigma':heap) (v:val) 
  (l:memory_location) (f:field),
  (forall l' f' v', read sigma l' f' v' -> P v') -> P v -> 
  write sigma l f v sigma' -> 
  (forall l' f' v', read sigma' l' f' v' -> P v').
Proof.
intros.
destruct (excluded_middle (l=l')).
destruct (excluded_middle (f=f')); subst.

assert (v=v') by 
  (eapply read_injective; [ eapply write_eq; eauto | eauto]).
subst; assumption.

eapply H; eapply write_diff_field_inv; eauto.

eapply H; eapply write_diff_loc_inv; eauto.
Qed.

Lemma write_coDom : 
  forall sigma sigma' l l' f f' v v',
  write sigma l f v sigma' -> read sigma' l' f' v' ->
  (v=v') \/ read sigma l' f' v'.
Proof.
intros.
destruct (excluded_middle (l=l')).
destruct (excluded_middle (f=f'));subst.

left.
eapply read_injective; eauto.
eapply write_eq; eauto.

right; eapply write_diff_field_inv;eauto.

right; eapply write_diff_loc_inv; eauto.
Qed.

Lemma write_diff : forall l f l' f' sigma sigma' w v,
  (l,f) <> (l',f') ->
  write sigma l f v sigma' ->
  sigma' l' = Some w ->
  exists m, sigma l' = Some m /\ m f' = w f'.
Proof.
intros.
unfold write in H0.
destruct H0 as [[? ?]  ?].
destruct H0.
destruct (excluded_middle (l=l')).
destruct (excluded_middle (f=f')); 
  subst.
elim H; reflexivity.
exists x.
split.
assumption.
assert (x f' = updateField x f v f').
symmetry.
apply updateField_diff.
assumption.
rewrite H4.
rewrite H3 in H1.
injection H1.
intro.
subst.
reflexivity.
generalize (H2 l' H4).
intro.
rewrite <- H5.
exists w.
auto.
Qed.

End DomainProp.

