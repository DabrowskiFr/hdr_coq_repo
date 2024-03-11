Require Export type_safety.
Open Scope type_scope.
Open Scope list_scope.

Module DisjointReachability (S:COUNTING_SEMANTIC).

  Module TS := TypeSafety S. Import TS  W3 W2 W1 DP T S.

Definition cinf_max (w w':cinf) :=
  match w with 
    | unknown => unknown
    | eq => match w' with |unknown => unknown | eq => eq end
  end.

Lemma cinf_max_prop (w w' : cinf) :
  cinf_max w w' = eq -> (w=eq /\ w'=eq).
Proof.
intros.
unfold cinf_max in H.
destruct w; destruct w'; auto.
Qed.


Definition proj (al:abstract_location) (H:abstract_mVect * abstract_lVect) : abstract_location :=
  let (A,F) := al in
    let (Om,Pi) := H in
      let F' := fun ppt => 
        (fun m c => cinf_max (fst (F ppt) m c) (Om m c),
          fun m c fl => cinf_max (snd (F ppt) m c fl) (Pi m c fl)) in
        (A,F').
              
Inductive abstract_heap_reach : 
  abstract_heap -> PPT -> abstract_location -> Prop :=
| abstract_heap_reach_root : forall Sigma A F ppt
  (H:In ppt A),
  abstract_heap_reach Sigma ppt (A,F)
| abstract_heap_reach_next : forall Sigma f A F ppt ppt'
  (H:abstract_heap_reach Sigma ppt (A,F))
  (H1:In ppt' A),
  abstract_heap_reach Sigma ppt 
  (proj (Sigma ppt' f) (F ppt')).

Definition eq_counters (ppt:PPT) : 
  (abstract_mVect*abstract_lVect) :=
  (fun m c => eq, fun m c fl => eq).

Lemma reach_safety : forall ls l l',
  heap_reach ls l l' ->
  forall Sigma,
    (forall sigma, In sigma ls -> heap_abs sigma Sigma) ->
    forall  a m i c om pi,
      l=(a, CP m i c om pi) ->
      exists al', abstract_heap_reach Sigma (m,i,c) al' /\
        location_abs (Loc l')  al' om pi.
Proof.
induction 1; intros; subst.
exists ((m,i,c)::nil,eq_counters).
split; constructor; auto using in_eq.

destruct (IHheap_reach _ H2 _ _ _ _ _ _ (refl_equal _)) as [al' [IH1 IH2]].
clear IHheap_reach.

unfold heap_abs in H2.
destruct l' as [a' [m' i' c' om' pi']].
generalize (H2 _ H' _ _ _ _ _ _ _ _ _ H0 H1).
intro Htarget.

destruct al' as (A',F').
exists (proj (Sigma (m',i',c') f) (F' (m',i',c'))).

split.

econstructor; eauto.
inv IH2; assumption.

unfold proj.
destruct (Sigma (m',i',c') f) as [A'' F''].
case_eq (F' (m',i',c')).
intros a0 a1 Ha.
destruct l'' as [a'' [m'' i'' c'' om'' pi'']].
constructor.
inv Htarget; auto.

intros.
inj H3.

inv Htarget.
generalize (cinf_max_prop _ _ H4).
intro.
destruct H3.
case_eq (F'' (m'',i'',c'')).
intros a2 a3 Hb.
rewrite Hb in H3, H4.
simpl in H3, H4.
generalize (H'0 a2 a3 Hb _ _ fl H3).
intro.
destruct H6.

inv IH2.
generalize (H'1 a0 a1 Ha _ _  fl H5).
intro.
destruct H8.
split.
omega.

intro.
simpl in H10.
generalize (cinf_max_prop _ _ H10).
intro.
destruct H11.
apply H9 in H12.
apply H7 in H11.
omega.
Qed.

Definition disjoint_reachability (ls:list heap) (A:PPT->Prop) (ppt:PPT) : Prop :=
  forall ppt1 ppt2 l l1 l2,
    A ppt1 ->
    A ppt2 ->
      match l with (_, CP m i c _ _) =>
        match l1 with (a1, CP m1 i1 c1 _ _) =>
          match l2 with (a2, CP m2 i2 c2 _ _) =>
            heap_reach ls l1 l ->
            heap_reach ls l2 l ->
            ppt=(m,i,c) ->
            ppt1=(m1,i1,c1) ->
            ppt2=(m2,i2,c2) ->
            a1=a2
            end
          end
      end.

Definition single_ppt (ppt:PPT) (fl:flow) 
  (H:abstract_mVect*abstract_lVect) :=
  match ppt with (m,i,c) =>
    match H with (Om,Pi) => 
    Om m c = eq /\ Pi m c fl = eq end end.

Definition abstract_disjoint_reachability (p:program) (Sigma:abstract_heap) (A:PPT->Prop) (ppt:PPT) : Prop :=
  forall m1 i1 c1 m2 i2 c2 al al0,
    A (m1,i1,c1) ->
    A (m2,i2,c2) ->
      match al with (A,F) =>
        match al0 with (A0,F0) =>
          In ppt A ->
          In ppt A0 ->
          abstract_heap_reach Sigma (m1,i1,c1) (A,F) ->
          abstract_heap_reach Sigma (m2,i2,c2) (A0,F0) ->
          ((m1,i1,c1)=(m2,i2,c2)
          /\ single_ppt (m1,i1,c1) (p.(loop) (m1,i1)) (F ppt)
          /\ single_ppt (m2,i2,c2) (p.(loop) (m2,i2)) (F0 ppt))
          end
      end.

Lemma heap_reach_inDom : forall ls l l',
  heap_reach ls l l' -> exists sigma, In sigma ls /\ inDom l sigma.
Proof.
  induction 1; eauto.
Qed.
          
Lemma disjointR_safety : forall p L ls sigma mu omg Sigma A ppt,
  coherent p (L,sigma,mu,omg) -> 
  (forall sigma', In sigma' ls -> forall o, inDom o sigma' -> inDom o sigma) ->
  (forall sigma, In sigma ls -> heap_abs sigma Sigma) ->
  abstract_disjoint_reachability p Sigma A ppt ->
  disjoint_reachability ls A ppt.
Proof.
unfold disjoint_reachability.
intros p L ls sigma mu omg Sigma A ppt H O1 H0 H1 ppt1 ppt2 l l1 l2 H3 H4.
destruct l as [a [ m i c om pi]].
destruct l1 as [a1 [m1 i1 c1 om1 pi1]].
destruct l2 as [a2 [m2 i2 c2 om2 pi2]].
intros.
subst.
generalize (reach_safety _ _ _ H2 _ H0 _ _ _ _ _ _ (refl_equal _)).
generalize (reach_safety _ _ _ H5 _ H0 _ _ _ _ _ _ (refl_equal _)).
intros.
destruct H6 as [al0 [ Ha Hb]].
destruct H7 as [al1 [Hc Hd]].

unfold abstract_disjoint_reachability in H1.
destruct al0 as (A0,F0).
destruct al1 as (A1,F1).
inv Hb.
inv Hd.
generalize (H1 m2 i2 c2 m1 i1 c1 (A0,F0) (A1,F1) H4 H3 H16 H17 Ha Hc).
clear H1.
intro.
destruct H1.
inj H1.
destruct H6.
simpl in H1.
simpl in H6.
case_eq (F0 (m,i,c)).
case_eq (F1 (m,i,c)).
intros.
rewrite H8 in H1.
rewrite H7 in H6.
destruct H1.
destruct H6.

unfold coherent in H.
assert (a1=a2).
apply (H a1 a2 m1 i1 c1 om1 om2 pi1 pi2); auto.
destruct (heap_reach_inDom _ _ _ H2) as [sigma1 [T1 T2]].
eauto.
destruct (heap_reach_inDom _ _ _ H5) as [sigma1 [T1 T2]].
eauto.

generalize (H' a4 a5 H8 m1 c1 (loop p (m1,i1)) H1).
generalize (H'0 a0 a3 H7 m1 c1 (loop p (m1,i1)) H6).
intuition; congruence.
generalize (H' a4 a5 H8 m1 c1 (loop p (m1,i1)) H1).
generalize (H'0 a0 a3 H7 m1 c1 (loop p (m1,i1)) H6).
intuition; congruence.
assumption.
Qed.

End DisjointReachability.