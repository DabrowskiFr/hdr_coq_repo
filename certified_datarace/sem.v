Require Export semantic.

Module Type CONTEXT.

  Parameter pcontext : Set. (* pointer context *)
  Parameter mcontext : Set. (* method context *)
  (* [make_new_context m i cid c] gives a new context for an object
     of class name [cid], created in a method [m], at line [i],
     in a context [c] *)
  Parameter make_new_context : method -> line -> classId -> mcontext -> pcontext.
  (* [make_call_context m i c c_this] gives a context for a call
     in a method [m], at line [i], in a context [c] and with a context
     [c_this] for the variable this *)
  Parameter make_call_context : method -> line -> mcontext -> pcontext -> mcontext.
  (* [get_class p c] gives the corresponding class of the object created
     in context [c], if any *)
  Parameter get_class : program -> pcontext -> option classId.

  Parameter class_make_new_context : forall p m i cid c,
    body m i = Some (New cid) ->
    get_class p (make_new_context m i cid c) = Some cid.

  Parameter init_mcontext : mcontext.
  Parameter init_pcontext : pcontext.

  Parameter class_init_pcontext : forall p,
    get_class p init_pcontext = Some p.(main_class).(c_name).

  Parameter eq_pcontext : forall c1 c2:pcontext, {c1=c2}+{c1<>c2}.
  Parameter eq_mcontext : forall c1 c2:mcontext, {c1=c2}+{c1<>c2}.

End CONTEXT.

Module Type SEMANTIC.

  Declare Module Import C : CONTEXT.

  Definition memory_location : Set := location * pcontext.
  Definition eq_memloc : forall x y : memory_location, {x=y}+{x<>y} :=
    eq_pair eq_pos eq_pcontext.
  Definition memory_location' : Set := location * option pcontext.
  Definition eq_memloc' : forall x y : memory_location', {x=y}+{x<>y} :=
    eq_pair eq_pos (eq_some eq_pcontext).

  Inductive val :Set := Null | Loc (m:memory_location).

  Definition local := var -> val.
  Definition subst (l:local) (x:var) (v:val) := 
    fun y => if eq_var x y then v else l y.

  Definition op_stack := list val.
  
  Definition heap := memory_location -> option (field -> val).

  Definition fresh (sigma:heap) (l:location) : Prop := 
    forall c, sigma (l,c) = None.

  Definition alloc (sigma:heap) (l:memory_location) (sigma':heap) : Prop :=
    (sigma l = None) /\
    (sigma' l = Some (fun _ => Null)) /\
    forall l', l <> l' -> sigma' l' = sigma l'.

  Definition read (sigma:heap) (l:memory_location) (f:field) (v:val) : Prop :=
    exists m, sigma l = Some m /\ m f = v.

  Definition updateField (m:field -> val) (f:field) (v:val) :=
    fun f' => if eq_pos f f' then v else m f'.

  Definition write
    (sigma:heap) (l:memory_location) (f:field) (v:val) (sigma':heap) : Prop :=
    (exists m, 
      sigma l = Some m /\
      sigma' l = Some (updateField m f v)) /\
    forall l', l<>l' -> sigma' l'=sigma l'.

  Definition frame := method * line * mcontext * op_stack * local.
  Definition call_stack := list frame.
  Definition threads := memory_location' -> option call_stack.

  Definition upd_thread (L:threads) (o:memory_location') (cs:call_stack) : threads :=
    fun o' => if eq_memloc' o o' then Some cs else L o'.

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
  
  Definition PPT := (method * line) * mcontext.

  Definition event := event_kind * PPT * field.
  Definition action := option (memory_location' * event * memory_location).
  (*************************************************)
  (* Lock *)
  (*************************************************)

  Section step.
    Variable p:program.
    
    Inductive step0 :
      memory_location' -> PPT -> instruction -> 
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
      step0 o ppt (Goto j) (i,s,rho,sigma) (j,s,rho,sigma) None.
    
    Inductive step1 :
      memory_location' -> (frame*heap) -> (frame*heap) -> action -> Prop :=
    | step1_ctx : forall e c i i' instr m o rho rho' s s' sigma sigma'  
      (HYP1 : m.(body) i = Some instr)
      (HYP2: step0 o (m,i,c) instr (i,s,rho,sigma) (i',s',rho',sigma') e),
      step1 o (m,i,c,s,rho,sigma) (m,i',c,s',rho',sigma') e
    | step1_new : forall a c cid i m o rho s sigma sigma'
      (HYP1 : m.(body) i = Some (New cid))
      (HYP2 : fresh sigma a)
      (HYP5 : alloc sigma (a,make_new_context m i cid c) sigma'),
      step1 o (m,i,c,s,rho,sigma) (m,next_line i,c,(Loc (a,make_new_context m i cid c))::s,rho,sigma') None.
    
    Inductive step2 : memory_location' -> (call_stack * heap) -> (call_stack * heap) -> action -> Prop :=
    | step2_ctx : forall e cs fr fr' o sigma sigma'
      (H:step1 o (fr,sigma) (fr',sigma') e), 
      step2 o (fr::cs,sigma) (fr'::cs,sigma') e
    | step2_invoke : forall m i mid args rtype s v_list rho1 m1 c1 c rho cs' sigma o cid o'
      (H0 : m.(body) i = Some (InvokeVirtual (MethSign mid args rtype)))
      (H1 : get_class p (snd o') = Some cid)
      (H2 : lookup p (MethSign mid args rtype) cid = Some m1)
      (H3 : c1 = make_call_context m i c (snd o'))
      (H8 : rho1 0 = Loc o')
      (H9 : forall x, 0<x<=length args -> 
        rho1 x =List.nth (length args -x) v_list Null)
      (H10 : forall x, length args < x ->  rho1 x = Null) 
      (H11 : length v_list = length args),
      step2 o ((m,i,c,v_list++(Loc o')::s,rho)::cs',sigma)  
              ((m1,0,c1,nil,rho1)::(m,S i,c,s,rho)::cs',sigma) None
    | step2_return :
      forall o m i c s rho cs sigma 
        (H:m.(body) i = Some Return),
        step2 o ((m,i,c,s,rho)::cs,sigma) (cs,sigma) None
    | step2_areturn : forall o m i c  v s rho s' rho' cs sigma m' i' c'
      (H:m.(body) i = Some AReturn),
      step2 o ((m,i,c,v::s,rho)::(m',i',c',s',rho')::cs,sigma) 
              ((m',i',c',v::s',rho')::cs,sigma) None.
    
    Inductive step3 : threads -> (memory_location'*call_stack*heap*lock) ->
      (threads*heap*lock) -> action -> Prop :=
    | step3_ctx : forall L cs o sigma mu cs' sigma' e
      (H:step2 o (cs,sigma) (cs',sigma') e),
      step3 L (o,cs,sigma,mu) (upd_thread L o cs',sigma',mu) e
    | step3_start : forall m i s m1 rho1 c1 L sigma lock c rho cs o o' cid
      (H0 : m.(body) i = Some Run)
      (H1 : get_class p (snd o') = Some cid)
      (H2 : lookup p run cid = Some m1)
      (H3 : c1 = make_call_context m i c (snd o'))
      (H8 : rho1 0 = Loc o')
      (H9 : forall x, rho1 (S x) = Null)
      (H10 : forall c, L (fst o',c) = None),
      step3 L (o,(m,i,c,Loc o'::s,rho)::cs,sigma,lock) 
      (upd_thread 
        (upd_thread L o ((m,next_line i,c,s,rho)::cs))
        (fst o',Some (snd o')) ((m1,0,c1,nil,rho1)::nil),sigma,lock)
      None
    | step3_enter :forall L m i mu mu' o o' c s rho cs sigma
      (H0 : m.(body) i = Some MonitorEnter)
      (H2 : acquire (fst o) (fst o') mu mu'),
      step3 L (o,(m,i,c,Loc o'::s,rho)::cs,sigma,mu)
              (upd_thread L o ((m,next_line i,c,s,rho)::cs),sigma,mu')
              None
    | step3_exit : forall L m i mu mu' o o' c s rho cs sigma 
      (H0 : m.(body) i = Some MonitorExit)
      (H2 : release (fst o) (fst o') mu mu'),
      step3 L (o,(m,i,c,Loc o'::s,rho)::cs,sigma,mu)
              (upd_thread L o ((m,next_line i,c,s,rho)::cs),sigma,mu')
              None.

    Inductive step : (threads*heap*lock) -> (threads*heap*lock) -> action -> Prop :=
    | step_inter : forall L L' fr cs o sigma mu sigma' mu' e
      (H:step3 L (o,fr::cs,sigma,mu) (L',sigma',mu') e)
      (H1:L o = Some (fr::cs)),
      step (L,sigma,mu) (L',sigma',mu') e.

    Definition wf_heap (sigma:heap) : Prop :=
      forall l c1 c2, sigma (l,c1) <> None -> sigma (l,c2) <> None -> c1=c2.
    
  End step.

  Definition run_address : location := 1%positive.
  
  Definition init_p (p:program) := make_new_context (foo p) 0 (main_class p).(c_name) init_mcontext.
  
  Definition sigma_init (p:program) : heap := 
    (fun l' => if eq_memloc l' (run_address,init_p p) then Some (fun f => Null) else None).
  
  Definition threads_init (p:program) : threads :=
    fun l => 
      if eq_memloc' l (run_address,None) then 
        Some ((main p,0,init_mcontext,nil,fun _ => Null)::nil) 
        else None.
  
  Definition init (p:program) : state :=
    (threads_init p, sigma_init p, (fun _ => Free)).

  Inductive reachable (p:program) : state -> Prop :=
  | reachable_0 : reachable p (init p)
  | reachable_next : 
    forall st st' e (H:reachable p st) (H':step p st st' e), reachable p st'.

  Inductive reachable_h (p:program) : list heap -> state -> Prop :=
  | reachable_h_0 : 
    reachable_h p (sigma_init p::nil) (init p)
  | reachable_h_next : forall st L sigma mu e l,
    reachable_h p l st -> 
    step p st (L,sigma,mu) e -> 
    reachable_h p (sigma::l) (L,sigma,mu).

  Inductive heap_reach (ls:list heap) : memory_location -> memory_location -> Prop :=
  | heap_reach_root: forall sigma l
    (H0:In sigma ls)
    (H:sigma l <> None),
    heap_reach ls l l
  | heap_reach_next : forall sigma l l' l'' m f
    (H':In sigma ls)
    (H:heap_reach ls l l')
    (H0:sigma l' = Some m)
    (H1:m f = Loc l''),
    heap_reach ls l l''.

  Inductive conflicting_actions : action -> action -> Prop :=
  | conflicting_actions_def : forall o1 o2 o' ppt1 ppt2 f k1 k2,
    o1<>o2 ->
    (k1=Put \/ k2=Put) ->
    conflicting_actions (Some (o1,(k2,ppt1,f),o')) (Some (o2,(k1,ppt2,f),o')).

  Inductive get_ppt (ppt:PPT) : action -> Prop :=
  | get_ppt_def : forall o f o' k, get_ppt ppt (Some (o,(k,ppt,f),o')).

  Inductive get_owner (o:memory_location') : action -> Prop :=
  | get_owner_def : forall ppt f o' k, get_owner o (Some (o,(k,ppt,f),o')).

  Inductive get_target (o:memory_location) : action -> Prop :=
  | get_target_def : forall o1 ppt f k, get_target o (Some (o1,(k,ppt,f),o)).

  Inductive race_without_context (p:program) (ppt1 ppt2:method*line) : Prop :=
    race_without_context_def : forall st st1 st2 a1 a2 c1 c2,
      reachable p st ->
      step p st st1 a1 ->
      step p st st2 a2 ->
      get_ppt (ppt1,c1) a1 ->
      get_ppt (ppt2,c2) a2 ->
      conflicting_actions a1 a2 ->
      race_without_context p ppt1 ppt2.

  Inductive race (p:program) (t1 t2:memory_location') (ppt1 ppt2:method*line*mcontext) : Prop :=
    races_def : forall st st1 st2 a1 a2,
      reachable p st ->
      step p st st1 a1 ->
      step p st st2 a2 ->
      get_ppt ppt1 a1 ->
      get_ppt ppt2 a2 ->
      get_owner t1 a1 ->
      get_owner t2 a2 ->
      conflicting_actions a1 a2 ->
      race p t1 t2 ppt1 ppt2.

End SEMANTIC.



Module MakeSemantic (CC:CONTEXT).

  Module Import C := CC.

  Definition memory_location : Set := location * pcontext.
  Definition eq_memloc : forall x y : memory_location, {x=y}+{x<>y} :=
    eq_pair eq_pos eq_pcontext.
  Definition memory_location' : Set := location * option pcontext.
  Definition eq_memloc' : forall x y : memory_location', {x=y}+{x<>y} :=
    eq_pair eq_pos (eq_some eq_pcontext).

  Inductive val :Set := Null | Loc (m:memory_location).

  Definition local := var -> val.
  Definition subst (l:local) (x:var) (v:val) := 
    fun y => if eq_var x y then v else l y.

  Definition op_stack := list val.
  
  Definition heap := memory_location -> option (field -> val).

  Definition fresh (sigma:heap) (l:location) : Prop := 
    forall c, sigma (l,c) = None.

  Definition alloc (sigma:heap) (l:memory_location) (sigma':heap) : Prop :=
    (sigma l = None) /\
    (sigma' l = Some (fun _ => Null)) /\
    forall l', l <> l' -> sigma' l' = sigma l'.

  Definition read (sigma:heap) (l:memory_location) (f:field) (v:val) : Prop :=
    exists m, sigma l = Some m /\ m f = v.

  Definition updateField (m:field -> val) (f:field) (v:val) :=
    fun f' => if eq_pos f f' then v else m f'.

  Definition write
    (sigma:heap) (l:memory_location) (f:field) (v:val) (sigma':heap) : Prop :=
    (exists m, 
      sigma l = Some m /\
      sigma' l = Some (updateField m f v)) /\
    forall l', l<>l' -> sigma' l'=sigma l'.

  Definition frame := method * line * mcontext * op_stack * local.
  Definition call_stack := list frame.
  Definition threads := memory_location' -> option call_stack.

  Definition upd_thread (L:threads) (o:memory_location') (cs:call_stack) : threads :=
    fun o' => if eq_memloc' o o' then Some cs else L o'.

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
  
  Definition PPT := (method * line) * mcontext.

  Definition event := event_kind * PPT * field.
  Definition action := option (memory_location' * event * memory_location).
  (*************************************************)
  (* Lock *)
  (*************************************************)

  Section step.
    Variable p:program.
    
    Inductive step0 :
      memory_location' -> PPT -> instruction -> 
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
      step0 o ppt (Goto j) (i,s,rho,sigma) (j,s,rho,sigma) None.
    
    Inductive step1 :
      memory_location' -> (frame*heap) -> (frame*heap) -> action -> Prop :=
    | step1_ctx : forall e c i i' instr m o rho rho' s s' sigma sigma'  
      (HYP1 : m.(body) i = Some instr)
      (HYP2: step0 o (m,i,c) instr (i,s,rho,sigma) (i',s',rho',sigma') e),
      step1 o (m,i,c,s,rho,sigma) (m,i',c,s',rho',sigma') e
    | step1_new : forall a c cid i m o rho s sigma sigma'
      (HYP1 : m.(body) i = Some (New cid))
      (HYP2 : fresh sigma a)
      (HYP5 : alloc sigma (a,make_new_context m i cid c) sigma'),
      step1 o (m,i,c,s,rho,sigma) (m,next_line i,c,(Loc (a,make_new_context m i cid c))::s,rho,sigma') None.
    
    Inductive step2 : memory_location' -> (call_stack * heap) -> (call_stack * heap) -> action -> Prop :=
    | step2_ctx : forall e cs fr fr' o sigma sigma'
      (H:step1 o (fr,sigma) (fr',sigma') e), 
      step2 o (fr::cs,sigma) (fr'::cs,sigma') e
    | step2_invoke : forall m i mid args rtype s v_list rho1 m1 c1 c rho cs' sigma o cid o'
      (H0 : m.(body) i = Some (InvokeVirtual (MethSign mid args rtype)))
      (H1 : get_class p (snd o') = Some cid)
      (H2 : lookup p (MethSign mid args rtype) cid = Some m1)
      (H3 : c1 = make_call_context m i c (snd o'))
      (H8 : rho1 0 = Loc o')
      (H9 : forall x, 0<x<=length args -> 
        rho1 x =List.nth (length args -x) v_list Null)
      (H10 : forall x, length args < x ->  rho1 x = Null) 
      (H11 : length v_list = length args),
      step2 o ((m,i,c,v_list++(Loc o')::s,rho)::cs',sigma)  
              ((m1,0,c1,nil,rho1)::(m,S i,c,s,rho)::cs',sigma) None
    | step2_return :
      forall o m i c s rho cs sigma 
        (H:m.(body) i = Some Return),
        step2 o ((m,i,c,s,rho)::cs,sigma) (cs,sigma) None
    | step2_areturn : forall o m i c  v s rho s' rho' cs sigma m' i' c'
      (H:m.(body) i = Some AReturn),
      step2 o ((m,i,c,v::s,rho)::(m',i',c',s',rho')::cs,sigma) 
              ((m',i',c',v::s',rho')::cs,sigma) None.
    
    Inductive step3 : threads -> (memory_location'*call_stack*heap*lock) ->
      (threads*heap*lock) -> action -> Prop :=
    | step3_ctx : forall L cs o sigma mu cs' sigma' e
      (H:step2 o (cs,sigma) (cs',sigma') e),
      step3 L (o,cs,sigma,mu) (upd_thread L o cs',sigma',mu) e
    | step3_start : forall m i s m1 rho1 c1 L sigma lock c rho cs o o' cid
      (H0 : m.(body) i = Some Run)
      (H1 : get_class p (snd o') = Some cid)
      (H2 : lookup p run cid = Some m1)
      (H3 : c1 = make_call_context m i c (snd o'))
      (H8 : rho1 0 = Loc o')
      (H9 : forall x, rho1 (S x) = Null)
      (H10 : forall c, L (fst o',c) = None),
      step3 L (o,(m,i,c,Loc o'::s,rho)::cs,sigma,lock) 
      (upd_thread 
        (upd_thread L o ((m,next_line i,c,s,rho)::cs))
        (fst o',Some (snd o')) ((m1,0,c1,nil,rho1)::nil),sigma,lock)
      None
    | step3_enter :forall L m i mu mu' o o' c s rho cs sigma
      (H0 : m.(body) i = Some MonitorEnter)
      (H2 : acquire (fst o) (fst o') mu mu'),
      step3 L (o,(m,i,c,Loc o'::s,rho)::cs,sigma,mu)
              (upd_thread L o ((m,next_line i,c,s,rho)::cs),sigma,mu')
              None
    | step3_exit : forall L m i mu mu' o o' c s rho cs sigma 
      (H0 : m.(body) i = Some MonitorExit)
      (H2 : release (fst o) (fst o') mu mu'),
      step3 L (o,(m,i,c,Loc o'::s,rho)::cs,sigma,mu)
              (upd_thread L o ((m,next_line i,c,s,rho)::cs),sigma,mu')
              None.

    Inductive step : (threads*heap*lock) -> (threads*heap*lock) -> action -> Prop :=
    | step_inter : forall L L' fr cs o sigma mu sigma' mu' e
      (H:step3 L (o,fr::cs,sigma,mu) (L',sigma',mu') e)
      (H1:L o = Some (fr::cs)),
      step (L,sigma,mu) (L',sigma',mu') e.

  End step.

  Definition run_address : location := 1%positive.

  Definition init_p (p:program) := make_new_context (foo p) 0 (main_class p).(c_name) init_mcontext.
  
  Definition sigma_init (p:program) : heap := 
    (fun l' => if eq_memloc l' (run_address,init_p p) then Some (fun f => Null) else None).
  
  Definition threads_init (p:program) : threads :=
    fun l => 
      if eq_memloc' l (run_address,None) then 
        Some ((main p,0,init_mcontext,nil,fun _ => Null)::nil) 
        else None.
  
  Definition init (p:program) : state :=
    (threads_init p, sigma_init p, (fun _ => Free)).

  Inductive reachable (p:program) : state -> Prop :=
  | reachable_0 : reachable p (init p)
  | reachable_next : 
    forall st st' e (H:reachable p st) (H':step p st st' e), reachable p st'.

  Inductive reachable_h (p:program) : list heap -> state -> Prop :=
  | reachable_h_0 : 
    reachable_h p (sigma_init p::nil) (init p)
  | reachable_h_next : forall st L sigma mu e l,
    reachable_h p l st -> 
    step p st (L,sigma,mu) e -> 
    reachable_h p (sigma::l) (L,sigma,mu).

  Inductive heap_reach (ls:list heap) : memory_location -> memory_location -> Prop :=
  | heap_reach_root: forall sigma l
    (H0:In sigma ls)
    (H:sigma l <> None),
    heap_reach ls l l
  | heap_reach_next : forall sigma l l' l'' m f
    (H':In sigma ls)
    (H:heap_reach ls l l')
    (H0:sigma l' = Some m)
    (H1:m f = Loc l''),
    heap_reach ls l l''.

  Definition wf_heap (sigma:heap) : Prop :=
    forall l c1 c2, sigma (l,c1) <> None -> sigma (l,c2) <> None -> c1=c2.

  Inductive conflicting_actions : action -> action -> Prop :=
  | conflicting_actions_def : forall o1 o2 o' ppt1 ppt2 f k1 k2,
    o1<>o2 ->
    (k1=Put \/ k2=Put) ->
    conflicting_actions (Some (o1,(k2,ppt1,f),o')) (Some (o2,(k1,ppt2,f),o')).

  Inductive get_ppt (ppt:PPT) : action -> Prop :=
  | get_ppt_def : forall o f o' k, get_ppt ppt (Some (o,(k,ppt,f),o')).

  Inductive get_owner (o:memory_location') : action -> Prop :=
  | get_owner_def : forall ppt f o' k, get_owner o (Some (o,(k,ppt,f),o')).

  Inductive get_target (o:memory_location) : action -> Prop :=
  | get_target_def : forall o1 ppt f k, get_target o (Some (o1,(k,ppt,f),o)).

  Inductive race_without_context (p:program) (ppt1 ppt2:method*line) : Prop :=
    race_without_context_def : forall st st1 st2 a1 a2 c1 c2,
      reachable p st ->
      step p st st1 a1 ->
      step p st st2 a2 ->
      get_ppt (ppt1,c1) a1 ->
      get_ppt (ppt2,c2) a2 ->
      conflicting_actions a1 a2 ->
      race_without_context p ppt1 ppt2.

  Inductive race (p:program) (t1 t2:memory_location') (ppt1 ppt2:method*line*mcontext) : Prop :=
    races_def : forall st st1 st2 a1 a2,
      reachable p st ->
      step p st st1 a1 ->
      step p st st2 a2 ->
      get_ppt ppt1 a1 ->
      get_ppt ppt2 a2 ->
      get_owner t1 a1 ->
      get_owner t2 a2 ->
      conflicting_actions a1 a2 ->
      race p t1 t2 ppt1 ppt2.

End MakeSemantic.










