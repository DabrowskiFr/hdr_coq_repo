Require Export counting_semantic.
Require Export Bool.

Module Types (S:COUNTING_SEMANTIC).

Import S C.

(* Abstract Domain *) 
Inductive cinf : Set := eq | unknown.

Definition abstract_mVect := method -> mcontext -> cinf.

Definition abstract_lVect := method -> mcontext -> flow -> cinf.

Definition abstract_location := 
  (list PPT) * (PPT -> abstract_mVect*abstract_lVect).

Definition abstract_op_stack := list abstract_location.

Definition abstract_local := var -> abstract_location.

Definition abstract_frame := abstract_op_stack * abstract_local.

Definition abstract_heap := PPT -> field -> abstract_location.

(* Subtyping *)

Definition lcinf (u1 u2:cinf) :=
  match u1 with
    | eq => True
    | unknow => u2=unknow
  end.

Definition labstract_mVect (aom aom':abstract_mVect) := 
  forall m c, lcinf (aom m c) (aom' m c).

Definition labstract_lVect (api api':abstract_lVect) := 
  forall m c fl, lcinf (api m c fl) (api' m c fl).

Definition labstract_value (al:abstract_location) (al':abstract_location) : Prop :=
  match al with (A,F) =>
    match al' with (A',F') =>
      ((forall ppt, In ppt A -> In ppt A') /\
      (forall ppt, In ppt A -> 
        match F ppt with (Om,Pi) => 
          match F' ppt with (Om',Pi') =>
            labstract_mVect Om Om' /\ labstract_lVect Pi Pi' end end))
    end
  end.

Inductive  labstract_op_stack : abstract_op_stack -> abstract_op_stack -> Prop :=
| labstract_op_stack_nil : labstract_op_stack nil nil
| labstract_op_stack_cons : forall al al' Os Os'
  (H:labstract_value al al')
  (H':labstract_op_stack Os Os'),
  labstract_op_stack (al::Os) (al'::Os').

Definition labstract_local (Gamma Gamma': abstract_local) :=
  forall x, labstract_value (Gamma x) (Gamma' x).

Definition labstract_frame (H H':abstract_frame) :=
  match H with (Os,Gamma) =>
    match H' with (Os',Gamma') => 
      labstract_op_stack Os Os' /\ labstract_local Gamma Gamma'
    end
  end.

(* Abstraction relations *)

Inductive location_abs:  val -> abstract_location -> mVect ->lVect ->Prop :=
| location_abs0 : forall al om pi, location_abs Null al om pi
| location_abs1 : forall a m i c (om om':mVect) (pi pi':lVect) A F
  (H:In (m,i,c) A)
  (H':forall Om api,
    F (m,i,c) = (Om,api) -> forall m' c' fl,
      Om m' c' = eq -> (om m' c' = om' m' c' /\
      (api m' c' fl = eq -> pi m' c' fl = pi' m' c' fl))
  ),
  location_abs (Loc (a,CP m i c om pi)) (A,F) om' pi'.

Definition heap_abs (sigma:heap) (Sigma:abstract_heap) : Prop :=
  forall a m i c om pi w f v,
  sigma (a,CP m i c om pi) = Some w -> w f = v -> location_abs v (Sigma (m,i,c) f) om pi.

Inductive op_stack_abs : op_stack -> abstract_op_stack -> mVect -> lVect -> Prop :=
| frame_abs_nil : forall om pi, op_stack_abs nil nil om pi
| frame_abs_cons : forall v s al S om pi
  (H:location_abs v al om pi)
  (H':op_stack_abs s S om pi),
  op_stack_abs (v::s) (al::S) om pi.

Definition local_abs (rho:local) (Gamma:abstract_local) (om:mVect) (pi:lVect) : Prop :=
  forall x, location_abs (rho x) (Gamma x) om pi.

Definition frame_abs (fr:frame) (Fr:abstract_frame) : Prop := 
  match fr with (CP m i c om pi,os,rho) => 
    match Fr with (Os,Gamma) =>
      op_stack_abs os Os om pi /\ local_abs rho Gamma om pi
    end
  end.



Definition kill_frame (m:method) (c:mcontext) (H:abstract_mVect*abstract_lVect) :=
  match H with (Om,Pi) =>
    let Om' := fun m' c' => if eq_mc (m,c) (m',c') then unknown else Om m' c' in
      let Pi' :=  fun m' c' fl => if eq_mc (m,c) (m',c') then unknown else Pi m' c' fl in
        (Om',Pi')
  end.

Definition kill_flow (m:method) (c:mcontext) (fl:flow) (H:abstract_mVect*abstract_lVect) :=
  match H with (Om,Pi) =>
    let Pi' := fun m' c' fl' => 
      if eq_mc (m,c)(m',c') then 
        if eq_flow fl fl' then unknown else Pi m' c' fl' 
        else Pi m' c' fl' in
          (Om,Pi')
  end.

Definition kill_frame_value (m:method) (c:mcontext) (al:abstract_location) :=
  match al with (A,F) => 
    (A, fun ppt => kill_frame m c (F ppt))
  end.

Definition kill_flow_value (m:method) (c:mcontext) (fl:flow) (al:abstract_location) :=
  match al with (A,F) => 
    (A, fun ppt => kill_flow m c fl (F ppt))
  end.

Fixpoint kill_frame_op_stack (m:method) (c:mcontext) (Os:abstract_op_stack) {struct Os}:=
  match Os with 
    | nil => nil
    | al::Os' => (kill_frame_value m c al)::(kill_frame_op_stack m c Os')
  end.

Definition kill_frame_local (m:method) (c:mcontext) (Gamma:abstract_local) :=
  fun x => kill_frame_value m c (Gamma x).

Fixpoint kill_flow_op_stack (m:method) (c:mcontext) (fl:flow) (Os:abstract_op_stack) {struct Os}:=
  match Os with 
    | nil => nil
    | al::Os' => (kill_flow_value m c fl al)::(kill_flow_op_stack m c fl Os')
  end.

Definition kill_flow_local (m:method) (c:mcontext) (fl:flow) (Gamma:abstract_local) :=
  fun x => kill_flow_value m c fl (Gamma x).

Definition kill_frame_frame (m:method) (c:mcontext) (Fr:abstract_frame) :=
  match Fr with (Os,Gamma) => (kill_frame_op_stack m c Os, kill_frame_local m c Gamma) end.

Definition kill_flow_frame (m:method) (c:mcontext) (fl:flow) (Fr:abstract_frame) :=
  match Fr with (Os,Gamma) => (kill_flow_op_stack m c fl Os, kill_flow_local m c fl Gamma) end.

Definition abstract_frames :=   PPT -> abstract_frame.

Definition abstract_signatures :=   
  method -> mcontext -> (abstract_location * list abstract_location * option abstract_location).

Inductive wtyped : instruction -> abstract_op_stack -> Prop :=
| wtyped_aconstnull : forall Os, wtyped AConstNull Os
| wtyped_new : forall Os cid, wtyped (New cid) Os
| wtyped_aload : forall Os x, wtyped (ALoad x) Os
| wtyped_astore : forall Os x al, wtyped (AStore x) (al::Os)
| wtyped_getfield : forall Os f al, wtyped (GetField f) (al::Os)
| wtyped_putfield : forall Os f al al', wtyped (PutField f) (al::al'::Os)
| wtyped_invoke : forall Os ms v_list al
  (H:length ms.(args)=length v_list),
  wtyped (InvokeVirtual ms) (v_list++al::Os)
| wtyped_return : forall Os, wtyped Return Os
| wtyped_areturn : forall Os al, wtyped AReturn (al::Os)
| wtyped_ifnd : forall Os i, wtyped (Ifnd i) Os
| wtyped_goto : forall Os i, wtyped (Goto i) Os
| wtyped_start : forall Os al, wtyped (Run) (al::Os)
| wtyped_monitorenter : forall Os al, wtyped (MonitorEnter) (al::Os)
| wtyped_montorexit : forall Os al, wtyped (MonitorExit) (al::Os).

Definition transfer := 
  instruction -> PPT -> abstract_frame -> abstract_frame.

Fixpoint points_to (l:list PPT) (f:field) (Sigma:abstract_heap) : (list PPT) :=
  match l with
    | nil => nil
    | ppt::l' => let (A,_) := Sigma ppt f in A++(points_to l' f Sigma)
  end.

Definition asubst (Gamma:abstract_local) (x:var) (al:abstract_location) :=
  fun y => if eq_var x y then al else Gamma y.

Definition eq_counters (ppt:PPT) : 
  (abstract_mVect*abstract_lVect) :=
  (fun m c => eq, fun m c fl => eq).


Definition diff_counters (ppt:PPT) : 
  (abstract_mVect*abstract_lVect) :=
  (fun m c => unknown, fun m c fl => unknown).


Definition cinf_max (w w':cinf) :=
  match w with 
    | unknown => unknown
    | eq => match w' with |unknown => unknown | eq => eq end
  end.


Definition proj (al:abstract_location) (H:abstract_mVect * abstract_lVect) : 
  abstract_location :=
  let (A,F) := al in
    let (Om,Pi) := H in
      let F' := fun ppt => 
        (fun m c => cinf_max (fst (F ppt) m c) (Om m c),
          fun m c fl => cinf_max (snd (F ppt) m c fl) (Pi m c fl)) in
        (A,F').


Inductive llist_value : list abstract_location -> list abstract_location -> Prop :=
| llist_value_nil : llist_value nil nil
| llist_value_cons : forall al al' l l'
  (H:labstract_value al al')
  (H0:llist_value l l'),
  llist_value (al::l) (al'::l')
    .

Definition fresh_counter (ppt:PPT) : (PPT -> abstract_mVect*abstract_lVect) :=
  match ppt with (m,i,c) =>
    fun ppt' => if eq_ppt ppt ppt' then
      (fun m' c' => eq,
        fun m' c' fl => if eq_mc (m,c) (m',c') then 
          if eq_flow (i,next_line i) fl then unknown else eq 
          else eq)
      else eq_counters ppt'
  end.

Definition abstract_local_of_list (o:abstract_location) (l:list abstract_location) :=
  fun x => 
    match x with
      | 0 => o
      | _ => if le_gt_dec x (length l) then nth (length l - x) l (nil,eq_counters) else (nil,eq_counters)
    end.

Definition invoke_reduce (rtype:option abstract_location)
  (Os Os' : abstract_op_stack) (Gamma Gamma':abstract_local)
  (m:method) (c:mcontext) :=
  match rtype with 
    | None => labstract_frame (Os,Gamma) (Os',Gamma')
    | Some al => labstract_frame 
      ((kill_frame_value m c al)::Os,Gamma) (Os',Gamma')
  end.

Section transfer.
  Variable p:program.
  Variable M:abstract_signatures.
  Variable Sigma:abstract_heap.
  Variable ppt:PPT.

  Inductive transfer_prop : 
    instruction -> abstract_frame -> abstract_frame -> Prop :=

  | transfer_aconstnull : forall Os Gamma Os' Gamma'
    (H:labstract_frame ((nil,diff_counters)::Os,Gamma) (Os',Gamma')),
    transfer_prop AConstNull (Os,Gamma) (Os',Gamma')

  | transfer_new : forall Os Gamma Os' Gamma' cid
    (H: labstract_frame ((ppt::nil,fresh_counter ppt)::Os,Gamma) (Os',Gamma')),
    transfer_prop (New cid) (Os,Gamma) (Os',Gamma')

  | transfer_aload : forall Os Gamma Os' Gamma' x
    (H: labstract_frame ((Gamma x)::Os,Gamma) (Os',Gamma')),
    transfer_prop (ALoad x) (Os,Gamma) (Os',Gamma')

  | transfer_astore : forall Os Gamma Os' Gamma' x al
    (H:labstract_frame (Os, asubst Gamma x al) (Os',Gamma')),
    transfer_prop (AStore x) (al::Os,Gamma) (Os',Gamma')

  | transfer_getfield : forall Os Gamma Os' Gamma' f A F
    (H: forall ppt A' F', In ppt A -> Sigma ppt f = (A',F') ->
      labstract_frame ((A',diff_counters)::Os,Gamma) (Os',Gamma')),
    transfer_prop (GetField f) ((A,F)::Os,Gamma) (Os',Gamma')

  | transfer_putfield : forall Os Gamma Os' Gamma' f A F al
    (H0: forall ppt, In ppt A -> labstract_value (proj al (F ppt)) (Sigma ppt f))
    (H : labstract_frame (Os,Gamma) (Os',Gamma')),
    transfer_prop (PutField f) (al::(A,F)::Os,Gamma) (Os',Gamma')

  | transfer_ifnd : forall Os Gamma Os' Gamma' i
    (H: labstract_frame (Os,Gamma) (Os',Gamma')),
    transfer_prop (Ifnd i) (Os,Gamma) (Os',Gamma')

  | transfer_goto : forall Os Gamma Os' Gamma' i
    (H: labstract_frame (Os,Gamma) (Os',Gamma')),
    transfer_prop (Goto i) (Os,Gamma) (Os',Gamma')

  | transfer_invoke : forall Os Os' Gamma Gamma' ms v_list A0 F0
    (H0 : length v_list = length ms.(args))
    (H1: forall m0 i0 c0 m' args rtype cId this, 
      match ppt with
        (m,i,c) =>
        In (m0,i0,c0) A0 -> body m0 i0 = Some (New cId) -> lookup p ms cId = Some m' ->
        M m' (make_call_context m i c (make_new_context m0 i0 cId c0)) = (this,args,rtype) ->
        labstract_local (abstract_local_of_list (A0,F0) v_list) 
        (abstract_local_of_list this args)
        /\ invoke_reduce rtype Os Os' Gamma Gamma' m' (make_call_context m i c (make_new_context m0 i0 cId c0))      
      end
    ),
    transfer_prop (InvokeVirtual ms) (v_list++(A0,F0)::Os,Gamma) (Os',Gamma')

  | transfer_run : forall Os Gamma Os' Gamma' A0 F0
    (H:forall m0 i0 c0 m' args rtype cId this,      
      match ppt with
        (m,i,c) =>
        In (m0,i0,c0) A0 ->  body m0 i0 = Some (New cId) -> lookup p run cId = Some m' ->
        M m' (make_call_context m i c (make_new_context m0 i0 cId c0))=(this,args,rtype) ->
        labstract_local (abstract_local_of_list (A0,F0) nil)
        (abstract_local_of_list this args)
        /\ labstract_frame (Os,Gamma) (Os',Gamma')
      end),
    transfer_prop Run ((A0,F0)::Os,Gamma) (Os',Gamma')

  | transfer_monitorenter : forall Os Gamma Os' Gamma' al
    (H:labstract_frame (Os,Gamma) (Os',Gamma')),
    transfer_prop MonitorEnter (al::Os,Gamma) (Os',Gamma')

  | transfer_monitorexit : forall Os Gamma Os' Gamma' al
    (H:labstract_frame (Os,Gamma) (Os',Gamma')),
    transfer_prop MonitorExit (al::Os,Gamma) (Os',Gamma')
    .
End transfer.


Inductive dynamic_typing : call_stack -> abstract_signatures -> abstract_frames -> Prop :=
| dynamic_typing_nil : forall M Frs, dynamic_typing nil M (Frs:abstract_frames)
| dynamic_typing_cons : forall m i c om pi s rho cs M Frs
  (H1: frame_abs (CP m i c om pi,s,rho) (Frs (m,i,c)) )
  (H: dynamic_typing_aux (snd (M m c)) m c cs M Frs),
  dynamic_typing ((CP m i c om pi,s,rho)::cs) M Frs
with dynamic_typing_aux : option abstract_location -> method -> mcontext ->
  call_stack -> abstract_signatures -> abstract_frames -> Prop :=
| dynaming_typing_aux_void : forall m c cs M Frs
  (H:dynamic_typing cs M Frs),
  dynamic_typing_aux None m c cs M Frs
| dynamic_typing_non_void : forall al m i c m' c' om pi s rho cs M Frs
  (H:forall Os Gamma, 
    Frs (m,i,c)=(Os,Gamma) ->
    exists al', exists Os',
      Os=al'::Os'
      /\ labstract_value (kill_frame_value m' c' al) al' 
      /\ frame_abs (CP m i c om pi,s,rho) (Os',Gamma))
  (H: dynamic_typing_aux (snd (M m c)) m c cs M Frs),
  dynamic_typing_aux (Some al) m' c' ((CP m i c om pi,s,rho)::cs) M Frs.
  
Definition dynamic_typing_threads (L:threads) (sigma:heap) (M:abstract_signatures) (Frs:abstract_frames) (Sigma:abstract_heap) :=
  forall l cs , L l = Some cs -> dynamic_typing cs M Frs 
    /\ heap_abs sigma Sigma.



Definition transfer_cond p (cg:method -> mcontext -> Prop) M Frs Sigma := 
  forall m c i j instr,
    cg m c -> 
    cflow m (i,j) -> 
    m.(body) i = Some instr ->
    transfer_prop p M Sigma (m,i,c) instr
    (kill_flow_frame m c (i,j) (Frs (m,i,c)))
    (Frs (m,j,c)).

Definition invoke_cond (M:abstract_signatures) Frs := 
  forall m c this args rtype,
    M m c = (this,args,rtype) ->   
    labstract_frame 
    (nil, kill_frame_local m c (abstract_local_of_list this args))
    (Frs (m,0,c)).

Definition return_cond (M:abstract_signatures) := 
  forall m c args rtype,
      M m c = (args,rtype) ->
      forall i, m.(body) i = Some Return ->
        rtype=None.

Definition areturn_cond (M:abstract_signatures) (Frs:abstract_frames) :=
  forall m c  args rtype,
      M m c =(args,rtype) ->
      forall i, m.(body) i = Some AReturn ->
        exists al',
          rtype = Some al'
          /\ forall Os Gamma, Frs (m,i,c)=(Os,Gamma) ->
            exists al, exists Os', Os=al::Os' /\ 
              labstract_value al al'.
      

Definition start_cond (M:abstract_signatures) (Frs:abstract_frames) := 
  forall m c args rtype A F,
       m.(signature) = run ->
       M m c = ((A,F),args,rtype) -> 
       rtype=None
         /\ 
         labstract_frame
         (nil,abstract_local_of_list (A,diff_counters) nil)
         (Frs (m,0,c)).

Definition main_cond p (M:abstract_signatures) 
  (Frs:abstract_frames) :=
  (snd (M (main p) init_mcontext)=None) /\
  let Gamma := 
    fun x => 
      match x with 
        |0 => ((main p,0,init_mcontext)::nil,diff_counters)
        | _ => (nil,diff_counters)
      end
      in
      labstract_frame
      (nil,Gamma)
      (Frs (main p,0,init_mcontext)).

Inductive typing : program -> (method -> mcontext -> Prop) -> abstract_signatures -> abstract_frames -> abstract_heap -> Prop :=
  | typing_def : forall p cg M Frs Sigma
    (H : transfer_cond p cg M Frs Sigma)
    (H0 : invoke_cond  M Frs)
    (H1 : return_cond  M)
    (H2 : areturn_cond  M Frs)
    (H3 : start_cond  M Frs)
    (H4: main_cond p M Frs),
    typing p cg M Frs Sigma.

End Types.