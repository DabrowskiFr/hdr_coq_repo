Require Export eq_syntax.
Require Export tactics.

Definition location := positive.
Inductive lockstate : Set := Free | Held (o:location) (q:nat).  
Inductive event_kind : Set := Get | Put.

Module Sem.
  Definition eq_memloc : forall x y : location, {x=y}+{x<>y} := eq_pos.
  Inductive val :Set := Null | Loc (m:location).

  Definition local := var -> val.
  Definition subst (l:local) (x:var) (v:val) := 
    fun y => if eq_var x y then v else l y.

  Definition op_stack := list val.
  
  Definition heap := location -> option (classId*(field -> val)).

  Definition fresh (sigma:heap) (l:location) : Prop := sigma l = None.

  Definition alloc (sigma:heap) (c:classId) (l:location) (sigma':heap) : Prop :=
    (sigma l = None) /\
    (sigma' l = Some (c,(fun _ => Null))) /\
    forall l', l <> l' -> sigma' l' = sigma l'.

  Definition read (sigma:heap) (l:location) (f:field) (v:val) : Prop :=
    exists m, sigma l = Some m /\ snd m f = v.

  Definition updateField (m:field -> val) (f:field) (v:val) :=
    fun f' => if eq_pos f f' then v else m f'.

  Definition write
    (sigma:heap) (l:location) (f:field) (v:val) (sigma':heap) : Prop :=
    (exists m, 
      sigma l = Some m /\
      sigma' l = Some (fst m,updateField (snd m) f v)) /\
    forall l', l<>l' -> sigma' l'=sigma l'.

  Definition frame := method * line * op_stack * local.
  Definition call_stack := list frame.
  Definition threads := location -> option call_stack.

  Definition upd_thread (L:threads) (o:location) (cs:call_stack) : threads :=
    fun o' => if eq_memloc o o' then Some cs else L o'.

  Definition lock := location -> lockstate.
  Definition acquire (o:location) (o':location) (mu:lock) (mu':lock) : Prop :=
    (forall o'', o''<>o' -> mu' o'' = mu o'') /\
    ((mu o' =Free /\ mu' o' =Held o 1) \/ 
      (exists n, mu o' = Held o n /\ mu' o' = Held o (S n))).
  Definition release (o:location) (o':location) (mu:lock) (mu':lock) : Prop :=
    (forall o'', o''<>o' -> mu' o'' = mu o'') /\
    ((mu o' = Held o 1 /\ mu' o' = Free) \/ 
      (exists n, mu o' = Held o (S (S n)) /\ mu' o' = Held o (S n))).
  
  Definition state := threads * heap * lock.
  
  Definition next_line : line -> line := S.
  
  Definition PPT := (method * line).

  Definition event := event_kind * PPT * field.
  Definition action := option (location * event * location).
  (*************************************************)
  (* Lock *)
  (*************************************************)

  Section step.
    Variable p:program.
    
    Inductive step0 :
      location -> PPT -> instruction -> 
      (line*op_stack*local*heap) -> (line*op_stack*local*heap) -> action -> 
      Prop :=
    | step0_aconstnull : forall o ppt i s rho sigma,
      step0 o ppt AConstNull 
      (i,s,rho,sigma) (next_line i,Null::s,rho,sigma) None
    | step0_aload : forall o ppt i s rho sigma x,
      step0 o ppt (ALoad x) 
      (i,s,rho,sigma) (next_line i,(rho x)::s,rho,sigma) None
    | step0_astore : forall o ppt i s rho sigma x v,
      step0 o ppt (AStore x) 
      (i,v::s,rho,sigma) (next_line i,s,(subst rho x v),sigma) None
    | step0_getfield : forall o o0 ppt f i s rho sigma v0 v
      (HYP1 : v0=Loc o0)
      (HYP2 : read sigma o0 f v),
      step0 o ppt (GetField f) 
      (i,v0::s,rho,sigma) (next_line i,v::s,rho,sigma) (Some (o,(Get,ppt,f),o0))
    | step0_putfield : forall o o0 ppt f i s rho sigma sigma' v0 v
      (HYP1 : v0= Loc o0)
      (HYP2 : write sigma o0 f v sigma'),
      step0 o ppt (PutField f) 
      (i,v::v0::s,rho,sigma) (next_line i,s,rho,sigma') (Some (o,(Put,ppt,f),o0))
    | step0_ifndl : forall o ppt j i s rho sigma,
      step0 o ppt (Ifnd j) (i,s,rho,sigma) (j,s,rho,sigma) None
    | step0_ifndr : forall o ppt j i s rho sigma,
      step0 o ppt (Ifnd j) (i,s,rho,sigma) (next_line i,s,rho,sigma) None
    | step0_goto : forall o ppt j i s rho sigma,
      step0 o ppt (Goto j) (i,s,rho,sigma) (j,s,rho,sigma) None
    | step0_new : forall ppt a cid i o rho s sigma sigma'
      (HYP2 : fresh sigma a)
      (HYP5 : alloc sigma cid a sigma'),
      step0 o ppt (New cid) (i,s,rho,sigma) (next_line i,(Loc a)::s,rho,sigma') None.
    
    Inductive step2 : location -> (call_stack * heap) -> (call_stack * heap) -> action -> Prop :=
    | step2_ctx : forall e cs m i i' s s' rho rho' o sigma sigma' instr
      (HYP1 : m.(body) i = Some instr)
      (H:step0 o (m,i) instr (i,s,rho,sigma) (i',s',rho',sigma') e), 
      step2 o ((m,i,s,rho)::cs,sigma) ((m,i',s',rho')::cs,sigma') e
    | step2_invoke : forall m i mid args rtype s v_list rho1 m1 rho cs' sigma o cid o' fd
      (H0 : m.(body) i = Some (InvokeVirtual (MethSign mid args rtype)))
      (H1 : sigma o' = Some (cid,fd))
      (H2 : lookup p (MethSign mid args rtype) cid = Some m1)
      (H8 : rho1 0 = Loc o')
      (H9 : forall x, 0<x<=length args -> 
        rho1 x =List.nth (length args -x) v_list Null)
      (H10 : forall x, length args < x ->  rho1 x = Null) 
      (H11 : length v_list = length args),
      step2 o ((m,i,v_list++(Loc o')::s,rho)::cs',sigma)  
              ((m1,0,nil,rho1)::(m,S i,s,rho)::cs',sigma) None
    | step2_return :
      forall o m i s rho cs sigma 
        (H:m.(body) i = Some Return),
        step2 o ((m,i,s,rho)::cs,sigma) (cs,sigma) None
    | step2_areturn : forall o m i v s rho s' rho' cs sigma m' i'
      (H:m.(body) i = Some AReturn),
      step2 o ((m,i,v::s,rho)::(m',i',s',rho')::cs,sigma) 
              ((m',i',v::s',rho')::cs,sigma) None.
    
    Inductive step3 : threads -> (location*call_stack*heap*lock) ->
      (threads*heap*lock) -> action -> Prop :=
    | step3_ctx : forall L cs o sigma mu cs' sigma' e
      (H:step2 o (cs,sigma) (cs',sigma') e),
      step3 L (o,cs,sigma,mu) (upd_thread L o cs',sigma',mu) e
    | step3_start : forall m i s m1 rho1 L sigma lock rho cs o o' cid fd
      (H0 : m.(body) i = Some Run)
      (H1 : sigma o' = Some (cid,fd))
      (H2 : lookup p run cid = Some m1)
      (H8 : rho1 0 = Loc o')
      (H9 : forall x, rho1 (S x) = Null)
      (H10 : L o' = None),
      step3 L (o,(m,i,Loc o'::s,rho)::cs,sigma,lock) 
      (upd_thread 
        (upd_thread L o ((m,next_line i,s,rho)::cs))
        o' ((m1,0,nil,rho1)::nil),sigma,lock)
      None
    | step3_enter :forall L m i mu mu' o o' s rho cs sigma
      (H0 : m.(body) i = Some MonitorEnter)
      (H2 : acquire o o' mu mu'),
      step3 L (o,(m,i,Loc o'::s,rho)::cs,sigma,mu)
              (upd_thread L o ((m,next_line i,s,rho)::cs),sigma,mu')
              None
    | step3_exit : forall L m i mu mu' o o' s rho cs sigma 
      (H0 : m.(body) i = Some MonitorExit)
      (H2 : release o o' mu mu'),
      step3 L (o,(m,i,Loc o'::s,rho)::cs,sigma,mu)
              (upd_thread L o ((m,next_line i,s,rho)::cs),sigma,mu')
              None.

    Inductive step : (threads*heap*lock) -> (threads*heap*lock) -> action -> Prop :=
    | step_inter : forall L L' fr cs o sigma mu sigma' mu' e
      (H:step3 L (o,fr::cs,sigma,mu) (L',sigma',mu') e)
      (H1:L o = Some (fr::cs)),
      step (L,sigma,mu) (L',sigma',mu') e.

  End step.

  Definition run_address : location := 1%positive.
  
  Definition sigma_init (p:program) : heap := 
    (fun l' => if eq_memloc l' run_address then Some (p.(main_class).(c_name),fun f => Null) else None).
  
  Definition threads_init (p:program) : threads :=
    fun l => 
      if eq_memloc l run_address then 
        Some ((main p,0,nil,fun _ => Null)::nil) 
        else None.
  
  Definition init (p:program) : state :=
    (threads_init p, sigma_init p, (fun _ => Free)).

  Inductive reachable (p:program) : state -> Prop :=
  | reachable_0 : reachable p (init p)
  | reachable_next : 
    forall st st' e (H:reachable p st) (H':step p st st' e), reachable p st'.

  Inductive conflicting_actions : action -> action -> Prop :=
  | conflicting_actions_def : forall o1 o2 o' ppt1 ppt2 f k1 k2,
    o1<>o2 ->
    (k1=Put \/ k2=Put) ->
    conflicting_actions (Some (o1,(k2,ppt1,f),o')) (Some (o2,(k1,ppt2,f),o')).

  Inductive get_ppt (ppt:PPT) : action -> Prop :=
  | get_ppt_def : forall o f o' k, get_ppt ppt (Some (o,(k,ppt,f),o')).

  Inductive get_owner (o:location) : action -> Prop :=
  | get_owner_def : forall ppt f o' k, get_owner o (Some (o,(k,ppt,f),o')).

  Inductive get_target (o:location) : action -> Prop :=
  | get_target_def : forall o1 ppt f k, get_target o (Some (o1,(k,ppt,f),o)).

  Inductive race (p:program) : PPT -> PPT -> Prop :=
    races_def : forall ppt1 ppt2 st st1 st2 a1 a2,
      reachable p st ->
      step p st st1 a1 ->
      step p st st2 a2 ->
      get_ppt ppt1 a1 ->
      get_ppt ppt2 a2 ->
      conflicting_actions a1 a2 ->
      race p ppt1 ppt2.

  Definition race_free (p:program) : Prop :=
    forall ppt1 ppt2, ~ race p ppt1 ppt2.

End Sem.

  Inductive conflicting_access : instruction -> instruction -> Prop :=
  | conflicting_access_read_write : forall f, conflicting_access (GetField f) (PutField f)
  | conflicting_access_write_read : forall f, conflicting_access (PutField f) (GetField f)
  | conflicting_access_write_write : forall f, conflicting_access (PutField f) (PutField f).

  Inductive OriginalPair : Sem.PPT -> Sem.PPT -> Prop :=
  | OriginalPair_def : forall m1 i1 ins1 m2 i2 ins2,
    body m1 i1 = Some ins1 ->
    body m2 i2 = Some ins2 ->
    conflicting_access ins1 ins2 ->
    OriginalPair (m1,i1) (m2,i2).

  Lemma OriginalPair_sound : forall p ppt1 ppt2,
    Sem.race p ppt1 ppt2 -> OriginalPair ppt1 ppt2.
  Proof.
    intros.
    inv H.
    inv H5; inv H3; inv H4.
    inv H2; inv H1.
    inv H3; inv H10.
    inv H14; inv H15.
    inv H10; inv H12.
    destruct H6; congruence.
    econstructor; eauto; constructor.
    econstructor; eauto; constructor.
    econstructor; eauto; constructor.
  Qed.








