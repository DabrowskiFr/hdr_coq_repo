Require Export counting_semantic_inv.
Require Export List.
Require Export remove_races.


Module MakeEscape (S:SEMANTIC) (CS:COUNTING_SEMANTIC with Module C := S.C).
  Module Import RR := RemoveRace S CS.
  Import DR TS.
  Module Import WFA := WF1 CS.
  Module Import WFB := WF2 CS.
  Module Import WFC := WF3 CS.
  Module Import DP := DomainProp CS.
  Import T.
  Import CS.
  Module CSI := CountingSemanticInv CS.

  
  Definition frame_roots (fr:frame) (l:memory_location) : Prop :=
    match fr with (cp, s, rho) =>
      In (Loc l) s \/ exists x, rho x = Loc l
    end.
  
  Inductive hreachable : memory_location -> memory_location -> heap -> Prop :=
  | hreachable_z : forall m sigma, hreachable m m sigma
  | hreachable_succ : forall m m' map f m'' sigma 
    (H : hreachable m m' sigma) (H0 : sigma m' = Some map) 
    (H1 : map f = Loc m''),
    hreachable m m'' sigma.
  
  Definition hreachable_from_frame (fr:frame) (l:memory_location) 
    (sigma:heap) :Prop :=
    exists l', frame_roots fr l' /\ hreachable l' l sigma.

  Definition current_turn (p:program) (fr:frame) (l:memory_location) : Prop :=
    match fr with (CP m i c om pi, s,rho) =>
      match l with (a0, CP m0 i0 c0 om0 pi0) =>
        m=m0 /\ c=c0 /\ 
        om m c = om0 m0 c0 /\ 
        pi m c (p.(loop) (m,i0)) = pi0 m0 c0 (p.(loop) (m,i0))
      end
    end.
  
  Definition abstract_current_turn (p:program) (ppt:PPT) (al : abstract_location) : Prop :=    
    match al with (A,F) =>
      forall m i c, In (m,i,c) A ->
        match F (m,i,c) with (Om,Pi) =>
          match ppt with (m',i',c') =>
            m' = m /\
            c' = c /\
            Om m c = eq /\ 
            Pi m c (p.(loop) (m,i)) = eq
          end
        end
    end.
      
  Definition abstract_escape := list PPT.
  
  Definition labstract_escape (e e' : abstract_escape) := 
    forall ppt, In ppt e' -> In ppt e.
  
  Definition abstract_escapes := PPT -> abstract_escape.
  
  Definition escape_abstraction_frame_frame 
    (p:program) (fr fr':frame) (sigma:heap) (E:abstract_escapes) : Prop :=
    match fr with (CP m i c om pi, s, rho) => forall a0 m0 i0 c0 om0 pi0, 
      In (m0,i0,c0) (E (m,i,c)) -> 
      inDom (a0, CP m0 i0 c0 om0 pi0) sigma -> 
      current_turn p fr (a0, CP m0 i0 c0 om0 pi0) -> 
      not (hreachable_from_frame fr' (a0, CP m0 i0 c0 om0 pi0) sigma)
    end.

  Definition return_point m i := 
    exists j, exists ms, cflow m (j,i) /\ m.(body) j = Some (InvokeVirtual ms).
      
  Inductive well_formed : call_stack -> Prop :=
  | on_call_nil : well_formed nil
  | on_call_top : forall fr cs
    (H : forall cp s rho, In (cp,s,rho) cs -> return_point (cp_m cp) (cp_i cp)),
      well_formed (fr::cs).

  Definition escape_abstraction (p:program) (L:threads) 
    (sigma:heap) (E:abstract_escapes) : Prop :=
    forall l l' cs cs' fr fr' ,
      l <> l' -> 
      L l = Some (fr::cs) -> L l' = Some cs' ->
      In fr' cs' ->
      escape_abstraction_frame_frame p fr fr' sigma E.
  
  Section Transfer.
    Variable p : program.
    Variable ppt : PPT.
    Variable Fr : abstract_frame.
    
    Definition is_local (ppt:PPT) (al:abstract_location) (e:abstract_escape) :=
      match al with (A,F) => 
        (forall ppt, In ppt A -> In ppt e) /\ abstract_current_turn p ppt al
      end.
    
    Inductive transfer_prop : instruction -> abstract_escape -> abstract_escape -> Prop :=
    (****************************************************************)
    (* Interesting instructions *)
    (****************************************************************)
    | transfer_new : forall cid e e'
      (H : labstract_escape (ppt::e) e'),
      transfer_prop (New cid) e e'
    | transfer_putfield_1 : forall al al' Os' f e e'
      (H : (fst Fr) = al::al'::Os')
      (H0 : is_local ppt al' e)
      (H1 : labstract_escape e e'),
      transfer_prop (PutField f)  e e'
    | transfer_putfield_2 : forall al al' Os' f e e'
      (H : (fst Fr) = al::al'::Os')
      (H0 : not (is_local ppt al' e))
      (H1 : labstract_escape nil e'),
      transfer_prop (PutField f)  e e'
    | transfer_invoke : forall ms e e'
      (H : labstract_escape nil e'),
      transfer_prop (InvokeVirtual ms)  e e'
    | transfer_run : forall e e'
      (H : labstract_escape nil e'),
      transfer_prop (Run) e e'  
    (****************************************************************)
    (* Other instructions *)      
    (****************************************************************)
    | transfer_aconstnull : forall e e'
      (H : labstract_escape e e'),
      transfer_prop AConstNull e e'
    | transfer_aload : forall x e e'
      (H : labstract_escape e e'),
      transfer_prop (ALoad x)  e e'
    | transfer_astore : forall x e e'
      (H : labstract_escape e e'),
      transfer_prop (AStore x)  e e'
    | transfer_getfield : forall f e e'
      (H : labstract_escape e e'),
      transfer_prop (GetField f)  e e'
    | transfer_ifnd : forall i e e'
      (H : labstract_escape e e'),
      transfer_prop (Ifnd i)  e e'
    | transfer_goto : forall i e e'
      (H : labstract_escape e e'),
      transfer_prop (Goto i)  e e' 
    | transfer_enter : forall e e'
      (H : labstract_escape e e'),
      transfer_prop (MonitorEnter)  e e'
    | transfer_exit : forall e e'
      (H : labstract_escape e e'),
      transfer_prop (MonitorExit)  e e'
      .
  End Transfer.
  
  Definition escape_typing (p:program) (Frs : abstract_frames) (E:abstract_escapes) := 
    forall m c,
      (labstract_escape nil (E (m,0,c))) /\    
      (forall i j, cflow m (i,j) -> forall instr, m.(body) i = Some instr -> 
        transfer_prop p (m,i,c) (Frs (m,i,c)) instr (E (m,i,c)) (E (m,j,c))).

  Lemma current_turn_1 : 
    forall p l m i i' c om pi s s' rho rho',
      local_coherency p l (CP m i c om pi) ->
      current_turn p (CP m i' c om (incr_lVect pi m c (i,i')), s',rho') l ->
      current_turn p (CP m i c om pi, s,rho) l.
  Proof.
    unfold current_turn, local_coherency.
    intros.    
    destruct l.
    destruct c0.
    destruct H0 as [Ha [Hb [Hc Hd]]].
    subst.
    rewrite Hc in *; clear Hc.
    generalize (H (refl_equal _) (refl_equal _) (refl_equal _)); clear H; intro.
    repeat split.
    rewrite <- Hd.
    assert ((i,i') <> (loop p (cp_m, cp_i))).
    intro.
    rewrite H0 in Hd.
    destruct (loop p (cp_m, cp_i)).
    rewrite incr_lVect_eq in Hd.
    omega.
    rewrite incr_lVect_diff; auto.
  Qed.    
  
  Lemma local_implies_current : forall p m i c om pi s rho l al e,
    location_abs (Loc l) al om pi-> 
    is_local p (m,i,c) al e -> 
    current_turn p (CP m i c om pi,s,rho) l.
  Proof.
    intros.
    unfold current_turn.
    destruct l as [a0 [m0 i0 c0 om0 pi0]].
    destruct al as [A0 F0].
    unfold is_local in H0.
    destruct H0.
    unfold abstract_current_turn in H1.

    inv H.
    case_eq (F0 (m0,i0,c0)); intros.
    generalize (H1 _ _ _ H12); intro; clear H1.
    rewrite H in H2.
    generalize (H' _ _ H); intro; clear H'.
    destruct H2 as [Ha [Hb [Hc Hd]]].
    subst.
    generalize (H1 m0 c0 (loop p (m0,i0)) Hc); intro; clear H1.
    destruct H2.
    generalize (H2 Hd); intro.
    auto.
  Qed.

  Lemma hreachable_inv : forall l l' sigma sigma',
    hreachable l l' sigma' ->
    (forall l', hreachable l l' sigma -> sigma' l' = sigma l') ->
    hreachable l l' sigma.
  Proof.
    induction 1.
    intro ; constructor.
    intro.
    generalize (IHhreachable H2); intro.
    generalize (H2 _ H3); intro.
    rewrite H4 in H0.
    eauto using hreachable_succ.
  Qed.


  Lemma hreachable_from_frame_inv : forall fr l sigma sigma',
    ~ hreachable_from_frame fr l sigma ->
    (forall l, hreachable_from_frame fr l sigma -> sigma' l = sigma l) ->
    ~ hreachable_from_frame fr l sigma'.
  Proof.
    intros.
    intro.
    elim H; clear H.
    unfold hreachable_from_frame in *.
    destruct H1.
    destruct H.
    exists x.
    split.
    assumption.
    eapply hreachable_inv.
    apply H1.
    intros.
    apply H0.
    exists x.
    auto.
  Qed.

  Lemma local_write_inv : forall fr l l' f v sigma sigma',
    ~ hreachable_from_frame fr l sigma ->
    write sigma l' f v sigma' -> ~ hreachable_from_frame fr l' sigma ->   
    ~ hreachable_from_frame fr l sigma'.
  Proof.
    intros.
    eapply hreachable_from_frame_inv.
    apply H.
    intros.
    assert (sigma' l0 = sigma l0).
    unfold write in H0.
    destruct H0.
    apply H3.
    intro.
    subst.
    intuition.
    assumption.
  Qed.

  Lemma current_inv : forall p m i j c om pi a0 i0 pi0 s rho,
    current_turn p (CP m j c om (incr_lVect pi m c (i,j)),s,rho) 
    (a0,CP m i0 c om pi0)  ->
    p.(loop) (m,i0) <> (i,j) ->
    current_turn p (CP m i c om pi,s,rho) (a0,CP m i0 c om pi0).
  Proof.
    unfold current_turn; intuition.
    unfold incr_lVect in *.
    unfold conv_lVect in *.
    rewrite LVect.get_upd2 in *; try congruence.
  Qed.

  Definition hreachable_from_thread (L:threads) l l' sigma:=
    exists cs, exists fr, 
      L l = Some cs /\ In fr cs /\ hreachable_from_frame fr l' sigma.

  Lemma reachable_closed_left : forall o1 o2 sigma,
    hreachable o1 o2 sigma ->
    forall o0 map f,
    sigma o0 = Some map ->
    map f = Loc o1 ->
    hreachable o0 o2 sigma.
  Proof.
    induction 1; intros.
    econstructor 2; eauto.
    constructor 1.
    econstructor 2; eauto.  
  Qed.

  Lemma hreachable_closed_exists : forall o1 o2 sigma,
    hreachable o1 o2 sigma ->
    o1 = o2 \/
    exists o0, exists map, exists f,
      sigma o1 = Some map /\
      map f = Loc o0 /\
      hreachable o0 o2 sigma.
  Proof.
    induction 1; intros.
    auto.
    right.
    destruct IHhreachable.
    subst; repeat (econstructor;eauto).
    destruct H2 as [o0 [map' [f' [T1 [T2 T3]]]]].
    repeat (econstructor;eauto).
  Qed.

  Lemma hreachable_write : forall l1 l2 sigma',
    hreachable l1 l2 sigma' ->
    forall l f v sigma,
      write sigma l f v sigma' ->
      hreachable l1 l2 sigma \/ 
      exists l', v = Loc l' /\ hreachable l' l2 sigma.
  Proof.
    induction 1.
    intros; left; constructor.
    intros.
    assert (R:=IHhreachable _ _ _ _ H2).
    destruct R.
    destruct H2 as [[map' [T3 T4]] H2].
    destruct (eq_memloc l m'); subst.
    rewrite H0 in T4; inv T4.
    unfold updateField in *.
    destruct eq_pos; subst.
    right; exists m''; split; auto.
    constructor.
    left.
    econstructor; eauto.
    left.
    rewrite H2 in H0; auto.
    econstructor; eauto.
    right.
    destruct H3 as [l' [L1 L2]]; subst.
    econstructor; split; eauto.
    destruct H2 as [[map' [T3 T4]] H2].
    destruct (eq_memloc l m'); subst.
    rewrite H0 in T4; inv T4.
    unfold updateField in *.
    destruct eq_pos; subst.
    inv H1; constructor.
    econstructor; eauto.
    rewrite H2 in H0; auto.
    econstructor; eauto.
  Qed.

  Lemma hreachable_alloc : forall l1 l2 sigma',
    hreachable l1 l2 sigma' ->
    forall l_new sigma,
      alloc sigma l_new sigma' ->
      hreachable l1 l2 sigma \/ 
      (~inDom l2 sigma /\ inDom l2 sigma').
  Proof.
    induction 1; intros.
    left; constructor.
    elim IHhreachable with (1:=H2); intros IH.
    destruct H2 as [T1 [T2 T3]].
    destruct (eq_memloc l_new m'); subst.
    rewrite H0 in T2; inv T2; congruence.
    rewrite T3 in H0; auto.
    left; econstructor; eauto.
    destruct H2 as [T1 [T2 T3]].
    destruct (eq_memloc l_new m'); subst.
    rewrite H0 in T2; inv T2; congruence.
    rewrite T3 in H0; auto.
    destruct IH.
    elim H2; unfold inDom; congruence.
  Qed.

  Lemma nth_In : forall l n r,
    nth n l Null = Loc r ->
    In (Loc r) l.
  Proof.
    induction l; simpl; intros.
    destruct n; congruence.
    destruct n; eauto.
  Qed.

  Opaque le_gt_dec.
  Lemma local_of_list_In : forall v l x r,
    local_of_list v l x = Loc r -> Loc r=v \/ In (Loc r) l.
  Proof.
    induction l; destruct x; simpl; intros; auto; try congruence.
    destruct le_gt_dec; try congruence.
    destruct le_gt_dec; try congruence.
    destruct (length l - x); auto.
    right; right; eapply nth_In; eauto.
  Qed.

  Lemma no_escape_if_local : forall p L l cs sigma mu omg L' sigma' mu' omg' e
    (HL: L l = Some cs),
    step3 p L (l,cs,sigma,mu,omg) (L',sigma',mu',omg') e ->
    forall l' cs' fr, L' l'=  Some cs'-> In fr cs' -> 
      forall l'', hreachable_from_frame fr l'' sigma' ->         
        hreachable_from_thread L l' l'' sigma \/
        hreachable_from_thread L l l'' sigma \/
        (~ inDom l'' sigma /\ inDom l'' sigma').
  Proof.
    unfold hreachable_from_thread, hreachable_from_frame; intros.
    destruct H2 as [l_fr [V1 V2]].
    inv H.
    inv H13.
    inv H9.
    unfold upd_thread in H0.
    destruct eq_memloc'; subst.
    inv H0.
    left.
    inv HYP2;
    try (match goal with
      [ id : L _ = Some (?cs) |- _ ] => exists cs end;
    simpl in H1; destruct H1; subst;
    [match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => exists fr; repeat split; auto with datatypes end;
    destruct V1; simpl in *;
    destruct H; try congruence; eauto|
    exists fr; repeat split; eauto with datatypes]).
    match goal with
      [ id : L _ = Some (?cs) |- _ ] => exists cs end.
    simpl in H1; destruct H1; subst.
    match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => exists fr; repeat split; auto with datatypes end.
    destruct V1; simpl in *.
    eauto.
    destruct H as [x0 H].
    unfold subst in *.
    destruct eq_var; subst; eauto.
    exists fr; repeat split; eauto with datatypes.
    exists o0; split; auto.
    destruct HYP3 as [map [T1 T2]].
    subst; eapply reachable_closed_left; eauto.
    match goal with
      [ id : L _ = Some (?cs) |- _ ] => exists cs end.
    simpl in H1; destruct H1; subst.
    match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => exists fr; repeat split; auto with datatypes end.
    elim hreachable_write with (1:=V2) (2:=HYP3); intros.
    destruct V1; simpl in *.
    exists l_fr; split; auto.
    eauto.
    destruct H as [l2 [V4 V3]]; subst.
    destruct V1; simpl in *; eauto.
    elim hreachable_write with (1:=V2) (2:=HYP3); intros.
    exists fr; repeat split; eauto with datatypes.
    destruct H0 as [ll' [W1 W2]]; subst.
    match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => exists fr; repeat split; auto with datatypes end.
    exists ll'; split.
    left; simpl; auto.
    auto.
    match goal with
      [ id : L _ = Some (?cs) |- _ ] => exists cs end.
    simpl in H1; destruct H1; subst.
    match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => exists fr; repeat split; auto with datatypes end.
    destruct V1; simpl in *; eauto with datatypes.
    exists fr; repeat split; auto with datatypes.
    eauto. 
    match goal with
      [ id : L _ = Some (?cs) |- _ ] => exists cs end.
    simpl in H1; destruct H1; subst.
    match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => exists fr; repeat split; auto with datatypes end.
    destruct V1; simpl in *; eauto with datatypes.
    exists fr; repeat split; auto with datatypes.
    eauto.     match goal with
      [ id : L _ = Some (?cs) |- _ ] => exists cs end.
    simpl in H1; destruct H1; subst.
    match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => exists fr; repeat split; auto with datatypes end.
    destruct V1; simpl in *; eauto with datatypes.
    exists fr; repeat split; auto with datatypes.
    eauto.
    inv HYP2;
    try (left;
    match goal with
      [ _ : L l' = Some ?cs ,
        _ : In ?fr ?cs |- _ ] => exists cs; exists fr; repeat split; eauto end; fail).
    elim hreachable_write with (1:=V2) (2:=HYP3); intros.
    left; 
    match goal with
      [ _ : L l' = Some ?cs ,
        _ : In ?fr ?cs |- _ ] => exists cs; exists fr; repeat split; eauto end.
    destruct H as [ll' [T1 T2]]; subst.
    right; left.
    match goal with
      [ _ : L l = Some (?fr::?cs) |- _ ] => exists (fr::cs); exists fr; repeat split; eauto with datatypes end.
    exists ll'; split; auto.
    left; auto with datatypes.
    (* new *)
    elim hreachable_alloc with (1:=V2)(2:=HYP5); intros.
    unfold upd_thread in *; destruct eq_memloc'; subst.
    inv H0.
    simpl in H1; destruct H1; subst.
    destruct V1.
    simpl in H0; destruct H0.
    inv H0.
    elim hreachable_closed_exists with (1:=H); intros.
    subst; right; right; split.
    unfold fresh, inDom in *; auto.
    destruct HYP5 as [ _ [T _]].
    intro; congruence.
    destruct H0 as [o0 [map [f [T1 [T2 T3]]]]].
    unfold fresh, inDom in *.
    elim (HYP2 (CP m i c om pi)).
    unfold code_pointer in *; rewrite T1; congruence.
    left; match goal with
      [ id : L l' = Some (?cs) |- _ ] => exists cs end.
    match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => exists fr; repeat split; auto with datatypes end.
    exists l_fr; split; auto.
    left; auto.
    left; match goal with
      [ id : L l' = Some (?cs) |- _ ] => exists cs end.
    match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => exists fr; repeat split; auto with datatypes end.
    exists l_fr; split; auto.
    right; auto.
    left; match goal with
      [ id : L l' = Some (?cs) |- _ ] => exists cs end.
    exists fr; repeat split; auto with datatypes.
    eauto.
    left.
    match goal with
      [ id : L l' = Some (?cs) |- _ ] => exists cs end.
    exists fr; repeat split; eauto with datatypes.
    right; right; auto.    
    (* invoke *)
    unfold upd_thread in *; destruct eq_memloc'; subst.
    inv H0.
    simpl in H1; destruct H1; subst.
    destruct V1.
    elim H.
    destruct H as [x H].
    elim local_of_list_In with (1:=H); clear H; intros H.
    left.
    match goal with
      [ id : L l' = Some (?cs) |- _ ] => exists cs end.    
    match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => exists fr; repeat split; auto with datatypes end.
    exists l_fr; split; auto.
    inv H; left; auto with datatypes.
    left.
    match goal with
      [ id : L l' = Some (?cs) |- _ ] => exists cs end.    
    match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => exists fr; repeat split; auto with datatypes end.
    exists l_fr; split; auto.
    left; auto with datatypes.
    destruct H.
    subst.
    left; match goal with
      [ id : L l' = Some (?cs) |- _ ] => exists cs end.    
    match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => exists fr; repeat split; auto with datatypes end.    
    exists l_fr; split; auto.
    destruct V1.
    left; eauto with datatypes.
    right; auto.
    left; match goal with
      [ id : L l' = Some (?cs) |- _ ] => exists cs end.    
    exists fr; repeat split; eauto with datatypes.    
    left; match goal with
      [ id : L l' = Some (?cs) |- _ ] => exists cs end.
    exists fr; repeat split; eauto with datatypes.    
    (* return *)
    unfold upd_thread in *; destruct eq_memloc'; subst.
    left; match goal with
      [ id : L l' = Some (?cs) |- _ ] => exists cs end.
    inv H0; exists fr; repeat split; eauto with datatypes.    
    left; match goal with
      [ id : L l' = Some (?cs) |- _ ] => exists cs end.
    exists fr; repeat split; eauto with datatypes.    
    (* return *)
    unfold upd_thread in *; destruct eq_memloc'; subst.
    left; match goal with
      [ id : L l' = Some (?cs) |- _ ] => exists cs end.
    inv H0.
    simpl in H1; destruct H1; subst.
    destruct V1.
    simpl in H; destruct H.
    match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => 
      exists fr; repeat split; auto with datatypes end.
    exists l_fr; split; auto.
    left; left; auto.
    match goal with
      [ id : L _ = Some (_::?fr::?cs) |- _ ] => 
      exists fr; repeat split; auto with datatypes end.
    exists l_fr; split; auto.
    left; auto.
    match goal with
      [ id : L _ = Some (_::?fr::?cs) |- _ ] => 
      exists fr; repeat split; auto with datatypes end.
    exists l_fr; split; auto.
    right; auto.
    exists fr; repeat split; eauto with datatypes.
    left; match goal with
      [ id : L l' = Some (?cs) |- _ ] => exists cs end.
    exists fr; repeat split; eauto with datatypes.
    (* Run *)
    unfold upd_thread in *.
    simpl in *.
    destruct eq_memloc'; subst.
    inv H0.
    simpl in H1; destruct H1.
    subst.
    right; left; match goal with
      [ id : L l = Some (?cs) |- _ ] => exists cs end.
    match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => 
      exists fr; repeat split; auto with datatypes end.
    exists l_fr; split; auto.
    unfold frame_roots in *;
    destruct V1; auto.
    elim H.
    destruct H as [ x H].
    elim local_of_list_In with (1:=H); intros.
    inv H0; eauto with datatypes.
    elim H0.
    intuition.
    destruct eq_memloc'; subst.
    inv H0.
    simpl in H1; destruct H1; subst.
    left; match goal with
      [ id : L _ = Some (?cs) |- _ ] => exists cs end.
    match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => 
      exists fr; repeat split; auto with datatypes end.
    unfold frame_roots in *;
    exists l_fr; split; auto.
    destruct V1; auto with datatypes.
    left; match goal with
      [ id : L _ = Some (?cs) |- _ ] => exists cs end.
    exists fr; repeat split; eauto with datatypes.
    left; exists cs'; exists fr; repeat split; eauto.
    (* monitorenter *)
    unfold upd_thread in *; destruct eq_memloc'; subst.
    inv H0.
    simpl in H1; destruct H1; subst.
    left.
    match goal with
      [ id : L _ = Some ?cs |- _ ] => exists cs end.
    match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => 
      exists fr; repeat split; auto with datatypes end.
    exists l_fr; split; auto.
    destruct V1; unfold frame_roots; auto with datatypes.
    left; match goal with
      [ id : L _ = Some ?cs |- _ ] => exists cs;
      exists fr; repeat split; eauto with datatypes end.
    left; match goal with
      [ id : L _ = Some ?cs |- _ ] => exists cs;
      exists fr; repeat split; eauto with datatypes end.
    (* monitorexit *)
    unfold upd_thread in *; destruct eq_memloc'; subst.
    inv H0.
    simpl in H1; destruct H1; subst.
    left.
    match goal with
      [ id : L _ = Some ?cs |- _ ] => exists cs end.
    match goal with
      [ id : L _ = Some (?fr::?cs) |- _ ] => 
      exists fr; repeat split; auto with datatypes end.
    exists l_fr; split; auto.
    destruct V1; unfold frame_roots; auto with datatypes.
    left; match goal with
      [ id : L _ = Some ?cs |- _ ] => exists cs;
      exists fr; repeat split; eauto with datatypes end.
    left; match goal with
      [ id : L _ = Some ?cs |- _ ] => exists cs;
      exists fr; repeat split; eauto with datatypes end.
  Qed.

Lemma inDom_hreachable : forall p st ,
  reachable p st -> 
  forall L sigma mu omg,
    st=(L,sigma,mu,omg) ->
    forall l cs, L l = Some cs ->
    forall fr, In fr cs -> 
      forall l', hreachable_from_frame fr l' sigma -> inDom l' sigma.
Proof.
  induction 1; intros.
  (* init *)
  unfold init in H; inv H.
  unfold threads_init in *.
  destruct eq_memloc'; inv H0.
  destruct H1; intuition; subst.
  destruct H2 as [l [T1 T2]].
  destruct T1; simpl in *; intuition.
  destruct H; congruence.
  (* main *)
  inv H'.

  assert (M:forall l, inDom l sigma0 -> inDom l sigma).
  clear IHreachable H H3 H2 H1; inv H7.
  intros; inv H4; try assumption.
  inv H13; try assumption.
  inv H10; try assumption.
  inv HYP2; try assumption.
  destruct HYP3 as [[m0 [T1 T2]] T3].
  intro; elim H.
  destruct (eq_memloc o1 l0); subst; try congruence.
  rewrite <- T3; auto.
  destruct HYP5 as [T1 [T2 T3]].
  intro; elim H.
  unfold fresh, inDom in *.
  destruct (eq_memloc (a, CP m i c om pi) l0); subst; try congruence.
  rewrite <- T3; auto.

  generalize (IHreachable _ _ _ _ (refl_equal _)); clear IHreachable; intros IH.
  inv H7.

  elim no_escape_if_local with (1:=H5) (2:=H4) (3:=H1) (4:=H2) (5:= H3); intros.
  destruct H0 as [cs1 [fr1 [T1 [T2 T3]]]].
  assert (IHH:=IH _ _ T1 _ T2 _ T3); auto.
  destruct H0.
  destruct H0 as [cs1 [fr1 [T1 [T2 T3]]]].
  assert (IHH:=IH _ _ T1 _ T2 _ T3); auto.
  intuition.
Qed.
  
Lemma reachable_well_formed : forall p st,  
  reachable p st ->  
  forall L sigma mu omg l cs, 
    st=(L,sigma,mu,omg) -> L l = Some cs -> well_formed cs.
Proof.
  induction 1; intros.
  (* init *)
  unfold init in H; inv H.
  unfold threads_init in *.
  destruct eq_memloc'; inv H0.
  constructor; intros.
  elim H.
  (* main *)
  subst; inv H'.
  generalize (IHreachable _ _ _ _ _ _ (refl_equal _) H8); intros IH.
  inv H7.
  inv H14.
  unfold upd_thread in H1; destruct eq_memloc'; subst.
  inv H1; constructor; inv IH; auto.
  generalize (IHreachable _ _ _ _ _ _ (refl_equal _) H1); auto.
  unfold upd_thread in H1; destruct eq_memloc'; subst.
  inv H1; constructor; inv IH.
  simpl; intros.
  destruct H0; auto.
  inv H0.
  simpl.
  do 3 (econstructor; eauto).
  eapply cflow_invoke; eauto.
  eauto.
  generalize (IHreachable _ _ _ _ _ _ (refl_equal _) H1); auto.
  unfold upd_thread in *; destruct eq_memloc'; subst; auto.
  inv H1.
  generalize (IHreachable _ _ _ _ _ _ (refl_equal _) H8); intros.
  inv H0; destruct cs; constructor; eauto with datatypes.
  generalize (IHreachable _ _ _ _ _ _ (refl_equal _) H1); auto.
  unfold upd_thread in *; destruct eq_memloc'; subst; auto.
  inv H1.
  generalize (IHreachable _ _ _ _ _ _ (refl_equal _) H8); intros.
  inv H0; constructor; eauto with datatypes.
  generalize (IHreachable _ _ _ _ _ _ (refl_equal _) H1); auto.
  unfold upd_thread in *; destruct eq_memloc'; subst; auto.
  inv H1.
  constructor; intros.
  elim H0.
  destruct eq_memloc'; subst; auto.
  inv H1.
  inv IH; constructor; auto.
  generalize (IHreachable _ _ _ _ _ _ (refl_equal _) H1); auto.
  unfold upd_thread in *; destruct eq_memloc'; subst; auto.
  inv H1.
  inv IH; constructor; eauto with datatypes.
  generalize (IHreachable _ _ _ _ _ _ (refl_equal _) H1); auto.
  unfold upd_thread in *; destruct eq_memloc'; subst; auto.
  inv H1.
  inv IH; constructor; eauto with datatypes.
  generalize (IHreachable _ _ _ _ _ _ (refl_equal _) H1); auto.
Qed.

Lemma aux : forall p L sigma mu omg,
  reachable p (L,sigma,mu,omg) ->
  forall a p1 p2, 
    sigma (a,p1) <> None -> sigma (a,p2) <> None -> p1=p2.
Proof.
  intros.
  eapply (CSI.wf_reach _ _ H); eauto.
Qed.

Theorem subject_reduction : forall p cg M Frs Sigma L L' mu mu' omg omg' sigma sigma' E e
  (HLoop : safe_loop p)
  (HCG : SafeCG p cg)
  (HTyp : typing p cg M Frs Sigma)
  (HTyping : escape_typing p Frs E)
  (HReachable_state : reachable p (L,sigma,mu,omg))
  (HAbs : escape_abstraction p L sigma E)
  (HStep : step p (L,sigma,mu,omg) (L',sigma',mu',omg') e),
  escape_abstraction p L' sigma' E.
Proof.
  unfold escape_abstraction.
  intros.
  assert (gunicity L) as HGunicity by (eapply reachable_gunicity;eauto).
  assert (coherent p (L',sigma',mu',omg')) as HCoherent by
    (eapply unicity; eauto using reachable_next).

  generalize (inDom_hreachable p (L,sigma,mu,omg) HReachable_state L _ _ _ (refl_equal _)); intro HReachable'.

  assert (reachable p (L',sigma',mu',omg')) as HReachableNew. 
  econstructor.
  apply HReachable_state.
  apply HStep.

  unfold escape_typing in *.
  inv HStep.
  MLtac' o l.
(* Current Thread *)
  inv H12.
  rewrite upd_thread_new in H0.
  inj H0.
  rewrite (upd_thread_old _ _ _ _ H) in H1.
  generalize (HAbs _ _ _ _ _ _ H H13 H1 H2); intro; clear HAbs.
  inv H16.
(* intraprocedural but New*)
  inv H14.
  generalize (HTyping m c); intro; clear HTyping.
  destruct H3.
  unfold escape_abstraction_frame_frame in *.
  intros.

  assert (current_turn p (CP m i c om pi, s, rho) (a0, CP m0 i0 c0 om0 pi0)).
  eapply current_turn_1.
  eapply reachable_local_coherency.
  apply HReachable_state.
  reflexivity.
  apply H13.
  apply in_eq.
  inv HYP2; (assumption || eapply write_dom_eq_inv; eauto).
  apply H7.
  (*eapply current_turn_1; eauto.
  eapply reachable_local_coherency;eauto using in_eq.
  eapply HCoherency; eauto using in_eq.
  inv HYP2; (assumption || eapply write_dom_eq_inv; eauto).*)

  assert (cflow m (i,i')) as HCFlow.
  inv HYP2.
  eapply cflow_aconstnull; eauto.
  eapply cflow_aload; eauto.
  eapply cflow_astore; eauto.
  eapply cflow_getfield; eauto.
  eapply cflow_putfield; eauto.
  eapply cflow_ifndr; eauto.
  eapply cflow_ifndl; eauto.
  eapply cflow_goto; eauto.

  generalize (H4 i i' HCFlow _ HYP1); intro; clear H4.
  inv HYP2; try (inv H9;auto).

(* PutField is_local*)

  assert (location_abs (Loc o0) al' om pi).
  assert (frame_abs (CP m i c om pi, v::Loc o0::s', rho') (Frs (m, i, c))).

  destruct (heap_abs_result_aux _ _ HReachable_state _ HCG _ _ _ 
    HTyp _ _ _ _ (refl_equal _)) as [HTypingu _]. 
  generalize (HTypingu l _ H13); intro.
  inv H4.
  assumption.


  unfold frame_abs in H4.
  unfold line in *; destruct (Frs (m,i,c)); simpl in H10; inv H10.
  destruct H4.
  inv H4.
  inv H'.
  assumption.


  assert (inDom o0 sigma).
  inv HYP3.
  destruct H9.
  destruct H9.
  unfold inDom.
  unfold code_pointer in *.
  intro.
  rewrite H9 in H16.
  discriminate.

  assert (~ hreachable_from_frame fr' o0 sigma).
  destruct o0 as [ a0' [m0' i0' c0' om0'  pi0']].
  destruct al' as (A0',F0').
  apply H0.
  unfold is_local in H11.
  destruct H11.
  inv H4.
  apply H11.
  assumption.

  assumption.
  eapply local_implies_current.
  apply H4.
  apply H11.
  generalize (H12 _ H5); intro Ha.
  assert (inDom (a0, CP m0 i0 c0 om0 pi0) sigma) by 
    (eapply write_dom_eq_inv; eauto).
  assert (~hreachable_from_frame fr' (a0, CP m0 i0 c0 om0 pi0) sigma) by auto.
  eapply local_write_inv; eauto.

(* PutField : not is_local *)
  apply H12 in H5.
  inv H5.

(* New *)
  unfold escape_abstraction_frame_frame.
  intros.

(* The fresh address is not reachable in the previous/current heap*)
  assert (~hreachable_from_frame fr' (a, CP m i c om pi) sigma).
  intro Ha.
  apply HReachable'  with (l:=l') (cs:=cs') in Ha.
  (*apply HReachable in Ha.*)
  unfold inDom in Ha.
  inv HYP5.
  rewrite H6 in Ha.
  intuition.
  assumption.
  assumption.

  assert (~hreachable_from_frame fr' (a, CP m i c om pi) sigma').
  eapply hreachable_from_frame_inv.
  apply H6.
  intros.
  inv HYP5.
  destruct H9.
  assert ((a, CP m i c om pi) <> l0).
  intro.
  rewrite H11 in H6.
  intuition.
  apply H10.
  assumption.

(* If the adress is the new address *)
  destruct (excluded_middle ((a,CP m i c om pi)=(a0, CP m0 i0 c0 om0 pi0))).
  inj H8.
  assumption.
(* Otherwise *)
(* If same allocation site*)
  unfold line in *.
  destruct (excluded_middle ((m,i,c) =(m0,i0,c0))).
(* Then contradiction *)
  assert ((a,CP m i c om pi)=(a0, CP m0 i0 c0 om0 pi0)).
  inj H9.
  unfold coherent in HCoherent.
  assert (inDom (a, CP m0 i0 c0 om pi) sigma').
  inv HYP5.
  destruct H10.
  unfold inDom.
  intro.
  rewrite H12 in H10.
  discriminate H10.  

 
  generalize H5; intro Hy.
  inv H5.
  destruct H11.
  destruct H11.
  assert (om0 m0 c0 = om m0 c0) as Hu by intuition.
  destruct (excluded_middle ((i0,next_line i0) <> p.(loop) (m0,i0))).
  rewrite incr_lVect_diff in H12.
      assert (pi0 m0 c0 (loop p (m0, i0)) = pi m0 c0 (loop p (m0, i0))) as Hv by intuition.
  generalize (HCoherent _ _ _ _ _ _ _ _ _ H4 H9 Hu Hv);intro Hw.
  rewrite Hw in *.
  clear Hw.
  unfold inDom in H4, H9.  
  generalize (aux p _ _ _ _ HReachableNew a (CP m0 i0 c0 om pi)(CP m0 i0 c0 om0 pi0) H9 H4) ;intro Hw.
  rewrite Hw.
  reflexivity.
  assumption.
  elim H14; clear H14; intro H14.
  generalize (incr_lVect_eq pi m0 c0 i0 (next_line i0)); intros.
  unfold line in *.
  rewrite H14 in H15, H12.
  rewrite H12 in H15.
  eapply current_turn_1 with (s:=Loc(a,CP m0 i0 c0 om0 pi0)::s) 
    (rho:=rho) in Hy.
  inv Hy.
  destruct H17.
  destruct H18.
  unfold line in *.
  rewrite <- H19 in H15.
  omega.

  eapply reachable_local_coherency. 
  apply HReachable_state.
  reflexivity.
  apply H13.
  apply in_eq.
  generalize (alloc_coDom  _ _ _ _ HYP5 H4); intro.
  destruct H16.
  elim H8.
  symmetry.
  assumption.
  assumption.
  elim H8.
  assumption.

  (*rewrite (HCoherent _ _ _ _ _ _ _ _ _ H4 H9) in *.
  rewrite H12 in H8.
  intuition.
  unfold current_turn in H11.
  destruct H11 as [Ha [Hb [Hc Hd]]].
  symmetry.
  assumption.
  symmetry.
  assumption.
  assumption.
  intuition.*)


  
  assert (In (m0,i0,c0) (E (m,i,c))).
  assert (cflow m (i, next_line i)) by (eapply cflow_new; eauto).
  generalize (HTyping m c); intro.
  destruct H11.
  generalize (H12 _ _ H10 _ HYP1); intro.
  inv H14.
  apply H16 in H3.
  destruct H3.
  intuition.
  assumption.

  assert (inDom (a0, CP m0 i0 c0 om0 pi0) sigma).
  generalize (alloc_coDom _ _ _ _ HYP5 H4);intro.
  destruct H11.
  elim H8.
  symmetry.
  assumption.
  assumption.

  unfold escape_abstraction_frame_frame in H0.

  assert (current_turn p (CP m i c om pi,s,rho) (a0, CP m0 i0 c0 om0 pi0)).
  eapply current_turn_1.
  eapply reachable_local_coherency.
  apply HReachable_state.
  reflexivity.
  apply H13.
  apply in_eq.
  assumption.

  (*eapply HCoherency.
  apply H13.
  apply in_eq.
  assumption.*)
  apply H5.
  generalize (H0 _ _ _ _ _ _ H10 H11 H12); intro.
  eapply hreachable_from_frame_inv.
  apply H14.
  intros.
  apply HReachable' with (l:=l') (cs:=cs') in H15.
  (*apply HReachable in H15.*)
  assert ((a, CP m i c om pi) <> l0).
  inv HYP5.
  unfold inDom in H15.
  intro.
  subst.
  rewrite H16 in H15.
  intuition.
  inv HYP5.
  apply H18 in H16.
  assumption.
  assumption.
  assumption.

  
(* invoke *)
  unfold escape_abstraction_frame_frame.
  intros.
  generalize (HTyping m1 (C.make_call_context m i c (C.make_new_context m0 i0 cId c0))); intro.
  destruct H6.
  apply H6 in H3.
  intuition.
(* return *)
  generalize (reachable_well_formed _ _ HReachable_state L _ _ _ _ _ (refl_equal _) H13);intro.
  (*generalize (reachable_well_formed _ _ _ _ _ HReachable_state l _ H13);intro.*)
  (*generalize (HWF l _ H13); intro.*)
  inv H3.
  destruct fr as [[cp' s'] rho'].
  assert (In (cp',s',rho') ((cp',s',rho')::cs)) by apply in_eq.
  generalize (H5 cp' s' rho' H3); intro.
  unfold return_point in H4.
  destruct H4 as [Ha [Hb [Hc Hd]]].
  generalize (HTyping (cp_m cp') (cp_c cp')); intro.
  destruct H4.
  unfold escape_abstraction_frame_frame.
  destruct cp'.
  intros.
  simpl in *.
  generalize (H6 _ _ Hc _ Hd); intro.
  inv H10.
  apply H14 in H7.
  intuition.

(* areturn *)
  generalize (reachable_well_formed _ _ HReachable_state L _ _ _ _ _ (refl_equal _) H13);intro.
  (*generalize (reachable_well_formed _ _ _ _ _ HReachable_state l _ H13);intro.*)
  (*generalize (HWF l _ H13); intro.*)
  inv H3.
  assert (In (p0, s', rho') ((p0, s', rho') :: cs))
    by (apply in_eq).
  apply H5 in H3.
  unfold return_point in H3.
  destruct H3 as [Ha [Hb [Hc Hd]]].
  generalize (HTyping (cp_m p0) (cp_c p0)); intro.
  destruct H3.
  unfold escape_abstraction_frame_frame.
  destruct p0.
  intros.
  simpl in H4.
  generalize (H4 _ _ Hc _ Hd);intro.
  inv H9.
  apply H11 in H6.
  intuition.

(* Run *)
  clear HCoherent.
  clear H1.
  simpl in H0.
  rewrite upd_thread_old in H0.
  rewrite upd_thread_new in H0.
  inj H0.
  unfold escape_abstraction_frame_frame.
  intros.
  generalize (HTyping m c); intros.
  destruct H4.
  assert (cflow m (i, next_line i)) by (eapply cflow_start; eauto).
  generalize (H5 _ _  H6 _ H16); intro.
  inv H7.
  apply H8 in H0.
  intuition.

  generalize (H25 (Some (CP m0 i0 c0 om0 pi0))); intro.
  simpl in H1.
  intro.
  unfold line in *.
  rewrite <- H3 in H13.
  unfold code_pointer in *.
  unfold line in *.
  rewrite H13 in H1.
  discriminate.

(*Enter *)
  unfold escape_abstraction_frame_frame.
  rewrite upd_thread_new in H0.
  inj H0.
  rewrite (upd_thread_old _ _ _ _ H) in H1.
  generalize (HAbs _ _ _ _ _ _ H H13 H1 H2); intro; clear HAbs.
  unfold escape_abstraction_frame_frame in *.
  intros.
  assert (current_turn p (CP m i c om pi, s, rho) (a0, CP m0 i0 c0 om0 pi0)).
  eapply current_turn_1.
  eapply reachable_local_coherency.
  clear HReachableNew.
  eauto.
  eauto.
  apply H13.
  apply in_eq.
  (*eapply HCoherency.
  apply H13.
  apply in_eq.*)
  apply H4.
  apply H5.
  apply H0.
  generalize (HTyping m c); intro.
  destruct H7.
  assert (cflow m (i, next_line i)) by (eapply cflow_monitorenter; eauto).
  generalize (H8 _ _ H9 _ H17); intro.
  inv H10.
  apply H11 in H3.
  assumption.
  assumption.
  assumption.
  auto.
(* Exit *)

  unfold escape_abstraction_frame_frame.
  rewrite upd_thread_new in H0.
  inj H0.
  rewrite (upd_thread_old _ _ _ _ H) in H1.
  generalize (HAbs _ _ _ _ _ _ H H13 H1 H2); intro; clear HAbs.
  unfold escape_abstraction_frame_frame in *.
  intros.
  assert (current_turn p (CP m i c om pi, s, rho) (a0, CP m0 i0 c0 om0 pi0)).
  eapply current_turn_1.
  clear HReachableNew.
  eapply reachable_local_coherency.
  eauto.
  eauto.
  apply H13.
  apply in_eq.
  (*eapply HCoherency.
  apply H13.
  apply in_eq.*)
  apply H4.
  apply H5.
  apply H0.
  generalize (HTyping m c); intro.
  destruct H7.
  assert (cflow m (i, next_line i)) by (eapply cflow_exit; eauto).
  generalize (H8 _ _ H9 _ H17); intro.
  inv H10.
  apply H11 in H3.
  assumption.
  assumption.
  assumption.

(* Other Thread *)
  unfold escape_abstraction_frame_frame.
  destruct fr as [[[m i c om pi] s] rho].
  red;intros.  
  destruct (excluded_middle (L l <> Some ((CP m i c om pi,s,rho)::cs))).
  inv H12.
  (* cas intra *)
  rewrite upd_thread_old in H0.
  rewrite H0 in H7.
  elim H7; reflexivity.
  assumption.

  (* cas run *)
  assert (i=0).
  destruct (excluded_middle (l=(a1,Some(CP m2 i2 c1 om1 pi1)))).
  subst.
  simpl in H0.
  rewrite upd_thread_new in H0.
  inj H0.
   reflexivity.
  rewrite upd_thread_old in H0.
  rewrite upd_thread_old in H0.
  rewrite H0 in H7.
  elim H7.
  reflexivity.
  assumption.
  intro.
  elim H8.
  rewrite <- H9.
  intuition.
  subst.
  generalize (HTyping m c); intro.
  destruct H8.
  unfold labstract_escape in H8.
  apply H8 in H3.
  inv H3.
   (* Enter *)
  rewrite upd_thread_old in H0.
  rewrite H0 in H7.
  elim H7; reflexivity.
  assumption.
  (* Exit *)
  rewrite upd_thread_old in H0.
  rewrite H0 in H7.
  elim H7; reflexivity.
  assumption.

  elim H7; clear H7; intro.
  elim no_escape_if_local with (2:=H12) (3:=H1) (4:=H2) (5:=H6); auto; intros.

  unfold hreachable_from_thread in H8.
  destruct H8 as [Ha [Hb [Hc [Hd He]]]].
  generalize (HAbs l l' cs Ha (CP m i c om pi,s,rho) Hb H H7 Hc Hd); intro.
  unfold escape_abstraction_frame_frame in H8.
  generalize (HReachable' _ _ Hc _ Hd _ He); intro.
  (*generalize (HReachable _ _ He); intro.*)
  generalize (H8 a0 m0 i0 c0 om0 pi0 H3 H9 H5); intro.
  intuition.

  (* Already reachable from the reduced thread *)
  destruct H8.
  unfold hreachable_from_thread in H8.
  destruct H8 as [Ha [Hb [Hc Hd]]].
  rewrite H13 in Hc.
  inj Hc.
  destruct Hd as [Hd He].
  
  assert (l <> o) by intuition.
  assert (In fr0 (fr0::cs0)) by (apply in_eq).
  generalize (HAbs l o cs (fr0::cs0) (CP m i c om pi,s,rho) Hb H8 H7 H13 Hd); intro.
  unfold escape_abstraction_frame_frame in H10.
  generalize (HReachable' _ _ H13 _ Hd _ He);intro.

  generalize (H10 a0 m0 i0 c0 om0 pi0 H3 H11 H5); intro.
  elim H14.
  assumption.

  (* L'addresse est nouvelle *)
  destruct H8 as [H8 _].
  inv H12.
  inv H22.
  inv H19.
  assert (inDom (a0, CP m0 i0 c0 om0 pi0) sigma).
  inv HYP2; try assumption.
  apply write_dom_eq_inv with (l:=o1) (f:=f) (v:=v) (sigma':=sigma'). 
  apply HYP3.
  apply H4.  
  elim H8; assumption.
  generalize (alloc_coDom sigma sigma' (a,CP m1 i1 c1 om1 pi1) 
    (a0, CP m0 i0 c0 om0 pi0) HYP5 H4); intro.
  destruct H9; [ | elim H8; assumption].
  inj H9.
  unfold gunicity in HGunicity.

  assert (dcounter (CP m i c om pi,s,rho) (CP m1 i1 c1 om1 pi1,s0,rho0)).
  assert (l<>o) by intuition.
  apply HGunicity with (l:=l) (l':=o) 
    (cs:=(CP m i c om pi,s,rho)::cs) (cs':=(CP m1 i1 c1 om1 pi1,s0,rho0)::cs0).
  assumption.
  assumption.
  assumption.
  apply in_eq.
  apply in_eq.
  unfold dcounter in H9.
  unfold current_turn in H5.
  destruct H5.
  destruct H10.
  destruct H11.
  generalize (H9 H5 H10); intro.
  subst.
  intuition.
  elim H8; assumption.
  elim H8;assumption.
  elim H8; assumption.
  elim H8; assumption.
  elim H8; assumption.
  elim H8; assumption.
Qed.


Theorem escape_safety : 
  forall p cg M Frs Sigma E (HCG:SafeCG p cg)  (HLoop:safe_loop p),
    typing p cg M Frs Sigma ->
    escape_typing p Frs E ->     
    forall st,
    reachable p st ->
    forall L sigma mu omg,
      st=(L,sigma,mu,omg) ->
      escape_abstraction p L sigma E.
Proof.
induction 5.
intros.
inj H1.
unfold escape_abstraction, escape_abstraction_frame_frame.
destruct fr as [ [ [ m i c  om pi ] s ] rho ].
intros.
unfold threads_init in H2.
MLtac' l (run_address,None:option code_pointer).
inj H2.
destruct (H0 (main p) (C.init_mcontext)).
apply H2 in H5.
inv H5.
discriminate.
intros.
destruct st as [[[L0 sigma0] mu0]omg0] .
rewrite H2 in *.
eapply subject_reduction;eauto.
Qed.

Import ML CPT PTR PT.

Inductive LocalAccess (p:program) (E:abstract_escape) : PPT -> abstract_op_stack -> Prop :=  
  | LocalAccess_Put : forall m i c a1 a2 s f,
    m.(body) i = Some (PutField f) ->
    is_local p (m,i,c) a2 E ->
    LocalAccess p E (m,i,c) (a1::a2::s)
  | LocalAccess_Get : forall m i c a s f,
    m.(body) i = Some (GetField f) ->
    is_local p (m,i,c) a E ->
    LocalAccess p E (m,i,c) (a::s).

Lemma head_In : forall (A:Type) (l:list A) (x:A), In x (x::l).
Proof.
  simpl; auto.
Qed.

Lemma LocalAccess_sound : forall p E PT M Frs Sigma ppt1 ppt2 a1 a2 st st1 st2,
  safe_loop p ->
  PointsToSpec p PT ->
  typing p PT.(ptM) M Frs Sigma ->
  escape_typing p Frs E ->     
  ValidReturns p ->
  LocalAccess p (E ppt1) ppt1 (fst (Frs ppt1)) ->
  reachable p st ->
  step p st st1 a1 ->
  step p st st2 a2 ->
  get_ppt ppt1 a1 ->
  get_ppt ppt2 a2 ->
  conflicting_actions a1 a2 -> 
  False.
Proof.
  intros p E PT M Frs Sigma ppt1 ppt2 a1 a2 st st1 st2 T T1 T2 T3 T4 H H0 H1 H2 H3 H4 H5.
  assert (S1:SafeCG p PT.(ptM)).
  unfold SafeCG.
  intros.
  eapply CPT.reachable_correct; eauto.
  destruct st as [[[L sigma] mu] omg].
  assert (ES:=escape_safety _ _ _ _ _ _ S1 T T2 T3 _ H0 _ _ _ _ (refl_equal _)).
  destruct (heap_abs_result_aux _ _ H0 _ S1 _ _ _ T2 _ _ _ _ (refl_equal _)) as [V1 _].
  assert (WF:=CSI.reachable_wf' _ _ H0).
  inv H1; inv H3.
  inv H12.
  inv H17.
  inv H14.
  inv HYP2.
  inv H; try congruence.
  assert (f0=f) by congruence; subst.
  generalize (V1 _ _ H13); clear V1; intros V.
  inv V.
  clear H18.
  case_eq (Frs (m, i, c)).
  intros Os Gamma HH; unfold line in *; rewrite HH in *.
  destruct H17 as [H17 _].
  inv H17.
  inv H8; clear H'.
  assert (current_turn p (CP m i c om pi,Loc o' :: s0,rho') o') by (eapply local_implies_current; eauto).
  inv H5.
  inv H2.
  inv H12.
  inv H21.
  inv H18.
  assert (o2=o) by (inv HYP2;auto); subst.
  assert (EZ:=ES o0 o _ _ _ _ H14 H13 H16 (head_In _ _ _)).
  simpl in EZ.
  destruct al as [A F]; destruct H9.
  inv H11.
  assert (In (m1,i1,c1) (E (m,i,c))) by auto.
  simpl in H.
  assert (inDom (a, CP m1 i1 c1 om1 pi1) sigma').
  assert (W1:=WF _ _ H13); clear WF.
  destruct W1 as [W1 _].
  assert (W2:CSI.wf1
      (CP m i c om pi, Loc (a, CP m1 i1 c1 om1 pi1) :: s0, rho', sigma'))
  by (eapply W1; eauto with datatypes).  
  unfold inDom; inv W2; eauto with datatypes.
  elim (EZ _ _ _ _ _ _ H3 H5 H).
  exists (a, CP m1 i1 c1 om1 pi1); repeat constructor.
  inv HYP2; auto with datatypes.
  (**)
  inv H; try congruence.
  assert (f0=f) by congruence; subst.
  generalize (V1 _ _ H13); clear V1; intros V.
  inv V.
  clear H18.
  case_eq (Frs (m, i, c)).
  intros Os Gamma HH; unfold line in *; rewrite HH in *.
  destruct H17 as [H17 _].
  inv H17.
  clear H11; inv H'.
  inv H8.
  assert (current_turn p (CP m i c om pi,v :: Loc o' :: s',rho') o') by
    (eapply local_implies_current; eauto).
  inv H5.
  inv H2.
  inv H12.
  inv H21.
  inv H18.
  assert (o2=o) by (inv HYP2;auto); subst.
  assert (EZ:=ES o0 o _ _ _ _ H14 H13 H16 (head_In _ _ _)).
  simpl in EZ.
  destruct al0 as [A F]; destruct H9.
  inv H11.
  assert (In (m1,i1,c1) (E (m,i,c))) by auto.
  simpl in H.
  assert (inDom (a, CP m1 i1 c1 om1 pi1) sigma).
  assert (W1:=WF _ _ H13); clear WF.
  destruct W1 as [W1 _].
  assert (W2:CSI.wf1
      (CP m i c om pi, v :: Loc (a, CP m1 i1 c1 om1 pi1) :: s', rho', sigma))
  by (eapply W1; eauto with datatypes).  
  unfold inDom; inv W2; eauto with datatypes.
  elim (EZ _ _ _ _ _ _ H3 H5 H).
  exists (a, CP m1 i1 c1 om1 pi1); repeat constructor.
  inv HYP2; auto with datatypes.
Qed.

Inductive EscapingPairs' (p:program) 
  (PT:pt) (ML:P.ml) 
  (Frs:abstract_frames) (Sigma:abstract_heap) (E:abstract_escapes)
  (ppt1 ppt2:PPT) : Prop :=
  EscapingPairs_def : 
    UnlockedPairs' p PT ML Sigma ppt1 ppt2 ->
    ~ LocalAccess p (E ppt1) ppt1 (fst (Frs ppt1)) ->
    ~ LocalAccess p (E ppt2) ppt2 (fst (Frs ppt2)) ->
    EscapingPairs' p PT ML Frs Sigma E ppt1 ppt2.

Theorem EscapingPairs'_sound : forall p PT ML M Frs Sigma E,
  safe_loop p ->
  PointsToSpec p PT ->
  P.MustLockSpec p PT.(ptL) PT.(ptM) ML ->
  typing p PT.(ptM) M Frs Sigma ->
  escape_typing p Frs E ->     
  ValidReturns p ->
  forall t1 t2 ppt1 ppt2,
    S.race p t1 t2 ppt1 ppt2 ->
    EscapingPairs' p PT ML Frs Sigma E ppt1 ppt2.
Proof.  
  intros.
  constructor.
  eapply UnlockedPairs'_sound; eauto.  
  elim RR.EInv.race_equiv with (1:=H5); intros t1' [t2' [T1 [T2 T3]]]; intro.  
  inv T1.
  eapply LocalAccess_sound with (a1:=a1) (a2:=a2); eauto.
  elim RR.EInv.race_equiv with (1:=H5); intros t1' [t2' [T1 [T2 T3]]]; intro.  
  inv T1.
  eapply LocalAccess_sound with (a1:=a2) (a2:=a1); eauto.
  inv H14; constructor; intuition.
Qed.

Definition EscapingPairs (p:program) (PT:pt) (ML:P.ml)
  (Frs:abstract_frames) (Sigma:abstract_heap) (E:abstract_escapes)
  (ppt1 ppt2:Sem.PPT) : Prop :=
  exists c1, exists c2,
    EscapingPairs' p PT ML Frs Sigma E (ppt1,c1) (ppt2,c2).

Theorem EscapingPairs_sound : forall p PT ML M Frs Sigma E,
  safe_loop p ->
  PointsToSpec p PT ->
  P.MustLockSpec p PT.(ptL) PT.(ptM) ML ->
  typing p PT.(ptM) M Frs Sigma ->
  escape_typing p Frs E ->     
  ValidReturns p ->
  forall ppt1 ppt2,
    Sem.race p ppt1 ppt2 ->
    EscapingPairs p PT ML Frs Sigma E ppt1 ppt2.
Proof.  
  intros.
  elim race_t_race with (1:=H5).
  intros t1 [t2 [c1 [c2 T]]].
  exists c1; exists c2.
  eapply EscapingPairs'_sound; eauto.
Qed.

End MakeEscape.

