Require Export EqNat.
Require Export ZArith.
Require Export sem.
Require Export assoc_list.

Record cp (A B C:Set) : Set := CP {
  cp_m : method;
  cp_i : line;
  cp_c : A;
  cp_om : B;
  cp_pi : C
}.
Implicit Arguments CP [A B C].

Lemma eq_cp : forall (A B C:Set),
  (forall x y:A, {x=y}+{x<>y}) ->
  (forall x y:B, {x=y}+{x<>y}) ->
  (forall x y:C, {x=y}+{x<>y}) ->
  forall x y:cp A B C, {x=y}+{x<>y}.
Proof.
  decide equality.
  apply eq_line.
  apply eq_method.
Qed.
Implicit Arguments eq_cp [A B C].
Implicit Arguments cp_m [A B C].
Implicit Arguments cp_i [A B C].
Implicit Arguments cp_c [A B C].
Implicit Arguments cp_om [A B C].
Implicit Arguments cp_pi [A B C].

Module Type COUNTING_SEMANTIC.

Declare Module Import C : CONTEXT.

Definition flow := line * line.

Module Domain_lVect.
  Definition domain : Set := method*mcontext*flow.
  Definition codomain : Set := nat.
  Definition eq_domain : forall x y:domain, {x=y}+{x<>y} :=
    eq_pair (eq_pair eq_method eq_mcontext) (eq_pair eq_line eq_line).
  Definition eq_codomain : forall x y:codomain, {x=y}+{x<>y} := eq_line.
  Definition def : codomain := O.
End Domain_lVect.
Module LVect := AssocList Domain_lVect.
Definition lVect := LVect.t.
Definition conv_lVect (pi:lVect) : method -> mcontext -> flow -> nat :=
  fun m c fl => LVect.get pi (m,c,fl).
Coercion conv_lVect : lVect >-> Funclass.

Module Domain_mVect.
  Definition domain : Set := method*mcontext.
  Definition codomain : Set := nat.
  Definition eq_domain : forall x y:domain, {x=y}+{x<>y} :=
    eq_pair eq_method eq_mcontext.
  Definition eq_codomain : forall x y:codomain, {x=y}+{x<>y} := eq_line.
  Definition def : codomain := O.
End Domain_mVect.
Module MVect := AssocList Domain_mVect.
Definition mVect := MVect.t.
Definition conv_mVect (om:mVect) : method -> mcontext -> nat :=
  fun m c => MVect.get om (m,c).
Coercion conv_mVect : mVect >-> Funclass.

Definition code_pointer : Set := cp mcontext mVect lVect.

Definition memory_location := location * code_pointer.
Definition eq_memloc : forall x y:memory_location, {x=y}+{x<>y} :=
  eq_pair eq_pos
    (eq_cp eq_mcontext MVect.eq LVect.eq).

Definition memory_location' := location * option code_pointer.
Definition eq_memloc' : forall x y:memory_location', {x=y}+{x<>y} :=
  eq_pair eq_pos
    (eq_some (eq_cp eq_mcontext MVect.eq LVect.eq)).

Inductive val :Set := Null | Loc (m:memory_location).

Definition local := var -> val.

Definition subst (l:local) (x:var) (v:val) := 
  fun y => if eq_var x y then v else l y.

Definition op_stack := list val.

Definition heap := memory_location -> option (field -> val).

Definition inDom (l:memory_location) (sigma:heap) : Prop :=  
  sigma l <> None.

Definition alloc (sigma:heap) (l:memory_location) (sigma':heap) : Prop :=
  (sigma l = None) /\
  (sigma' l = Some (fun _ => Null)) /\
  forall l', l <> l' -> sigma' l' = sigma l'.

Definition read (sigma:heap) (l:memory_location) (f:field) (v:val) : Prop :=
  exists m, sigma l = Some m /\ m f = v.

Definition updateField (m:field -> val) (f:field) (v:val) :=
  fun f' => if eq_pos f f' then v else m f'.

Definition fieldMap_p2p (P:val-> Prop) (m:field -> val) :=
  forall f, P (m f).

Definition write
  (sigma:heap) (l:memory_location) (f:field) (v:val) (sigma':heap) : Prop :=
  (exists m, 
    sigma l = Some m /\
    sigma' l = Some (updateField m f v)) /\
  forall l', l<>l' -> sigma' l'=sigma l'.

Definition heap_p2p (P:val -> Prop) (sigma:heap) :=
  forall l f v, read sigma l f v -> P v.

Definition frame := code_pointer * op_stack * local.
Definition call_stack := list frame.
Definition threads := memory_location' -> option call_stack.

Definition lock := location -> lockstate.
Definition state := threads * heap * lock * mVect.

Definition next_line : line -> line := S.

Ltac Ccase x x' := destruct (eq_mcontext x x');intros.

Definition eq_mc: forall x y : method*mcontext, {x=y}+{x<>y} :=
    eq_pair eq_method eq_mcontext.

Ltac MCcase x x' := destruct (eq_mc x x');intros.

Ltac Flcase x x' := destruct (eq_flow x x'); intros.

(* Definition of labels *)
(*************************************************)
Definition PPT := method * line * mcontext.

Definition eq_ppt : forall x y : PPT, {x=y}+{x<>y} :=
    eq_pair (eq_pair eq_method eq_line) eq_mcontext.

(* lVect *)
(**********************************************************************)
Definition incr_lVect (pi:lVect) (m:method) (c:mcontext) (fl:flow) :lVect
  :=  LVect.upd pi (m,c,fl) (S (LVect.get pi (m,c,fl))).

Definition incr_mVect (om:mVect) (m:method) (c:mcontext) : mVect :=
  MVect.upd om (m,c) (S (MVect.get om (m,c))).

Definition event := event_kind * PPT * field.
Definition action := option (memory_location' * event * memory_location).
(*************************************************)
(* Lock *)
(*************************************************)
Definition acquire (o:location) (o':location)
  (mu:lock) (mu':lock) : Prop :=
  (forall o'', o''<>o' -> mu'(o'')=mu(o'')) /\
  ((mu(o')=Free /\ mu'(o')=Held o 1) \/ 
    (exists n, mu(o')=Held o n /\ mu'(o')=Held o (S n))).

Definition release (o:location) (o':location)
  (mu:lock) (mu':lock) : Prop :=
  (forall o'', o''<>o' -> mu'(o'')=mu(o'')) /\
  ((mu(o')=Held o 1 /\ mu'(o')=Free) \/ 
    (exists n, mu(o')=Held o (S (S n)) /\ mu'(o')=Held o (S n))).

(*************************************************)
Definition local_of_list (this:val) (l:list val) :=
  fun x => 
    match x with
      | 0 => this
      | _ => if le_gt_dec x (length l) then nth (length l - x) l Null else Null
    end.

Definition invoke_mVect (om:mVect) (m:method) (c:mcontext) (omg:mVect) :=
  MVect.upd om (m,c) (S (MVect.get omg (m,c))).
Definition invoke_lVect (pi:lVect) (m:method) (c:mcontext) :=
  LVect.clear (fun mcfl => if eq_mc (fst mcfl) (m,c) then true else false) pi.
(*************************************************)

Definition fresh (sigma:heap) (a:location) : Prop :=
  forall p, not (inDom (a,p) sigma).

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
  | step1_ctx : forall c e i i' instr m o om 
    pi pi' rho rho' s s' sigma sigma'  
    (HYP1 : m.(body) i = Some instr)
    (HYP2: step0 o (m,i,c) instr (i,s,rho,sigma) (i',s',rho',sigma') e)
    (HYP3: pi'=incr_lVect pi m c (i,i')),
    step1 o ((CP m i c om pi,s,rho),sigma) 
    ((CP m i' c om pi',s',rho'),sigma') e
  | step1_new : forall a c cid i m o o' om pi pi' rho s sigma sigma'
    (HYP1 : m.(body) i = Some (New cid))
    (HYP2 : fresh sigma a)
    (HYP3 : o'=(a,(CP m i c om pi)))
    (HYP4 : pi'=incr_lVect pi m c (i,next_line i))
    (HYP5 : alloc sigma o' sigma'),
    step1 o ((CP m i c om pi,s),rho,sigma) 
    ((CP m (next_line i) c om pi',(Loc o')::s,rho),sigma') None.
  
  Inductive step2 :
    memory_location' -> (call_stack * heap * mVect) -> 
    (call_stack * heap * mVect) -> action -> Prop :=
  | step2_ctx : forall e cs fr fr' o omg sigma sigma'
    (H:step1 o (fr,sigma) (fr',sigma') e), 
    step2 o (fr::cs,sigma,omg) (fr'::cs,sigma',omg) e
  | step2_invoke : forall m i mid args rtype s s' v_list
    a0 m0 i0 c0 om0 pi0 m1 c1 om1 pi1 rho1 omg omg' om pi pi' c 
    rho cs' sigma o cId
    (H0 : m.(body) i = Some (InvokeVirtual (MethSign mid args rtype)))
    (H1 : s=v_list++(Loc (a0,CP m0 i0 c0 om0 pi0)::s'))
    (C0 : body m0 i0 = Some (New cId))
    (H2 : lookup p (MethSign mid args rtype) cId = Some m1)
    (H3 : c1=make_call_context m i c (make_new_context m0 i0 cId c0))
    (H4: om1 = invoke_mVect om m1 c1 omg)
    (H5: pi1 = invoke_lVect pi' m1 c1)  
    (H8: rho1=local_of_list (Loc (a0, CP m0 i0 c0 om0 pi0)) v_list)   
    (H10 : pi'=incr_lVect pi m c (i,S i))
    (H11 : omg' = incr_mVect omg m1 c1)
    (H12 : length v_list = length args),
    step2 o ((CP m i c om pi,s,rho)::cs',sigma,omg)  
    ((CP m1 0 c1 om1 pi1,nil,rho1)::
      (CP m (S i) c om pi',s',rho)::cs',sigma,omg') None
  | step2_return :
    forall o m i c om pi s rho cs sigma omg
      (H:m.(body) i = Some Return),
      step2 o ((CP m i c om pi,s,rho)::cs,sigma,omg) (cs,sigma,omg) None
  | step2_areturn : forall o m i c om pi v s rho s' rho' cs sigma omg p
    (H:m.(body) i = Some AReturn),
    step2 o ((CP m i c om pi,v::s,rho)::(p,s',rho')::cs,sigma,omg) 
    ((p,v::s',rho')::cs,sigma,omg) None.
  
  Definition upd_thread (L:threads) (o:memory_location') (cs:call_stack) : threads :=
    fun o' =>
      if eq_memloc' o o' then Some cs else L o'.

  Inductive step3 : threads -> (memory_location'*call_stack*heap*lock*mVect) ->
    (threads*heap*lock*mVect) -> action -> Prop :=
  | step3_ctx : forall L cs o sigma mu omg cs' sigma' omg' e
    (H:step2 o (cs,sigma,omg) (cs',sigma',omg') e),
    step3 L (o,cs,sigma,mu,omg) (upd_thread L o cs',sigma',mu,omg') e
  | step3_start : forall m i s a0 m0 i0 c0 om0 pi0 s' m1
    c1 om1 rho1 pi' L sigma lock omg c om pi rho cs o pi1 o' cId
    (H0 : m.(body) i = Some Run)
    (H1 : s=(Loc o')::s')
    (HO : o'=(a0,CP m0 i0 c0 om0 pi0))
    (C0 : body m0 i0 = Some (New cId))
    (H2 : lookup p (run) cId = Some m1)
    (H3 : c1=make_call_context m i c (make_new_context m0 i0 cId c0))
    (H4 : om1 = invoke_mVect MVect.init m1 c1 omg)
    (H5 : pi1 = LVect.init)
    (H8 : rho1 = local_of_list (Loc o') nil)
    (H9 : pi'=incr_lVect pi m c (i,S i))
    (H10 : forall c, L (fst o',c) = None),
    step3 L (o,(CP m i c om pi,s,rho)::cs,sigma,lock,omg) 
            (upd_thread 
              (upd_thread L o ((CP m (next_line i) c om pi',s',rho)::cs))
              (fst o',Some (snd o')) ((CP m1 0 c1 om1 pi1,nil,rho1)::nil),sigma,lock,incr_mVect omg m1 c1) 
            None
  | step3_enter :
    forall L m i mu mu' (o:memory_location') (o':memory_location) c om pi pi' s rho cs sigma omg
      (H0 : m.(body) i = Some MonitorEnter)
      (H2 : acquire (fst o) (fst o') mu mu')
      (H3 : pi'=incr_lVect pi m c (i,S i)),
      step3 L (o,(CP m i c om pi, (Loc o')::s,rho)::cs,sigma,mu,omg)
           (upd_thread L o ((CP m (next_line i) c om pi',s,rho)::cs),sigma,mu',omg)
           None
  | step3_exit :
    forall L m i mu mu' o o' c om pi pi' s rho cs sigma omg
      (H0 : m.(body) i = Some MonitorExit)
      (H2 : release (fst o) (fst o') mu mu')
      (H3 : pi'=incr_lVect pi m c (i,S i)),
      step3 L (o,(CP m i c om pi, (Loc o')::s,rho)::cs,sigma,mu,omg)
              (upd_thread L o ((CP m (next_line i) c om pi',s,rho)::cs),sigma,mu',omg)
              None.

  Inductive step : (threads*heap*lock*mVect) -> (threads*heap*lock*mVect) -> action -> Prop :=
  | step_inter :
    forall L L' fr cs o sigma mu omg sigma' mu' omg' e
      (H:step3 L (o,fr::cs,sigma,mu,omg) (L',sigma',mu',omg') e)
      (H1:L o = Some (fr::cs)),
      step (L,sigma,mu,omg) (L',sigma',mu',omg') e.
End step.

Definition om_init (p:program) : mVect :=  MVect.upd MVect.init (p.(main),init_mcontext) 1.
Definition cp_init (p:program) := (CP p.(main) 0 init_mcontext (om_init p) LVect.init).

Definition om_run_address (p:program) : mVect :=  MVect.init.
Definition cp_run_address (p:program) := (CP p.(foo) 0 init_mcontext (om_run_address p) LVect.init).

Definition run_address := 1%positive.

Definition sigma_init (p:program) : heap := 
  (fun l' => if eq_memloc l' (run_address,cp_run_address p) then Some (fun f => Null) else None).

Definition threads_init (p:program) : threads :=
  fun l => 
    if eq_memloc' l (run_address, None) then 
      Some ((cp_init p,nil,(fun _ => Null))::nil) 
      else None.

Definition init (p:program) : state :=
  (threads_init p, sigma_init p, (fun _ => Free), om_init p).

Inductive reachable (p:program) : state -> Prop :=
| reachable_0 : reachable p (init p)
| reachable_next : 
  forall st st' e (H:reachable p st) (H':step p st st' e), reachable p st'.

Inductive reachable_h (p:program) : list heap -> state -> Prop :=
| reachable_h_0 : 
  reachable_h p (sigma_init p::nil) (init p)
| reachable_h_next : forall st L sigma mu omg e l,
  reachable_h p l st -> 
  step p st (L,sigma,mu,omg) e -> 
  reachable_h p (sigma::l) (L,sigma,mu,omg).

Inductive heap_reach (ls:list heap) : memory_location -> memory_location -> Prop :=
| heap_reach_root: forall sigma l
  (H0:In sigma ls)
  (H:inDom l sigma),
  heap_reach ls l l
| heap_reach_next : forall sigma l l' l'' m f
  (H':In sigma ls)
  (H:heap_reach ls l l')
  (H0:sigma l' = Some m)
  (H1:m f = Loc l''),
  heap_reach ls l l''.
 

(******** Data races *********)

  Inductive conflicting_actions : action -> action -> Prop :=
  | conflicting_actions_def : forall o1 o2 o' ppt1 ppt2 f k1 k2,
    o1<>o2 ->
    (k1=Put \/ k2=Put) ->
    conflicting_actions (Some (o1,(k2,ppt1,f),o')) (Some (o2,(k1,ppt2,f),o')).


Inductive Races (p:program) (st:state) (a1 a2:action) : Prop :=
  Races_def : forall st1 st2,
    reachable p st ->
    step p st st1 a1 ->
    step p st st2 a2 ->
    a1<>a2 ->
    conflicting_actions a1 a2 ->
    Races p st a1 a2.

Inductive get_ppt (ppt:PPT) : action -> Prop :=
| get_ppt_def : forall o f o' k, get_ppt ppt (Some (o,(k,ppt,f),o')).

Inductive get_owner (o:memory_location') : action -> Prop :=
| get_owner_def : forall ppt f o' k, get_owner o (Some (o,(k,ppt,f),o')).

Inductive get_target (o:memory_location) : action -> Prop :=
| get_target_def : forall o1 ppt f k, get_target o (Some (o1,(k,ppt,f),o)).

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

End COUNTING_SEMANTIC.


Module CountingSemantic (CC:CONTEXT).

  Module Import C := CC.

Definition flow := line * line.

Module Domain_lVect.
  Definition domain : Set := method*mcontext*flow.
  Definition codomain : Set := nat.
  Definition eq_domain : forall x y:domain, {x=y}+{x<>y} :=
    eq_pair (eq_pair eq_method eq_mcontext) (eq_pair eq_line eq_line).
  Definition eq_codomain : forall x y:codomain, {x=y}+{x<>y} := eq_line.
  Definition def : codomain := O.
End Domain_lVect.
Module LVect := AssocList Domain_lVect.
Definition lVect := LVect.t.
Definition conv_lVect (pi:lVect) : method -> mcontext -> flow -> nat :=
  fun m c fl => LVect.get pi (m,c,fl).
Coercion conv_lVect : lVect >-> Funclass.

Module Domain_mVect.
  Definition domain : Set := method*mcontext.
  Definition codomain : Set := nat.
  Definition eq_domain : forall x y:domain, {x=y}+{x<>y} :=
    eq_pair eq_method eq_mcontext.
  Definition eq_codomain : forall x y:codomain, {x=y}+{x<>y} := eq_line.
  Definition def : codomain := O.
End Domain_mVect.
Module MVect := AssocList Domain_mVect.
Definition mVect := MVect.t.
Definition conv_mVect (om:mVect) : method -> mcontext -> nat :=
  fun m c => MVect.get om (m,c).
Coercion conv_mVect : mVect >-> Funclass.

Definition code_pointer : Set := cp mcontext mVect lVect.

Definition memory_location := location * code_pointer.
Definition eq_memloc : forall x y:memory_location, {x=y}+{x<>y} :=
  eq_pair eq_pos
    (eq_cp eq_mcontext MVect.eq LVect.eq).

Definition memory_location' := location * option code_pointer.
Definition eq_memloc' : forall x y:memory_location', {x=y}+{x<>y} :=
  eq_pair eq_pos
    (eq_some (eq_cp eq_mcontext MVect.eq LVect.eq)).

Inductive val :Set := Null | Loc (m:memory_location).

Definition local := var -> val.

Definition subst (l:local) (x:var) (v:val) := 
  fun y => if eq_var x y then v else l y.

Definition op_stack := list val.

Definition heap := memory_location -> option (field -> val).

Definition inDom (l:memory_location) (sigma:heap) : Prop :=  
  sigma l <> None.

Definition alloc (sigma:heap) (l:memory_location) (sigma':heap) : Prop :=
  (sigma l = None) /\
  (sigma' l = Some (fun _ => Null)) /\
  forall l', l <> l' -> sigma' l' = sigma l'.

Definition read (sigma:heap) (l:memory_location) (f:field) (v:val) : Prop :=
  exists m, sigma l = Some m /\ m f = v.

Definition updateField (m:field -> val) (f:field) (v:val) :=
  fun f' => if eq_pos f f' then v else m f'.

Definition fieldMap_p2p (P:val-> Prop) (m:field -> val) :=
  forall f, P (m f).

Definition write
  (sigma:heap) (l:memory_location) (f:field) (v:val) (sigma':heap) : Prop :=
  (exists m, 
    sigma l = Some m /\
    sigma' l = Some (updateField m f v)) /\
  forall l', l<>l' -> sigma' l'=sigma l'.

Definition heap_p2p (P:val -> Prop) (sigma:heap) :=
  forall l f v, read sigma l f v -> P v.

Definition frame := code_pointer * op_stack * local.
Definition call_stack := list frame.
Definition threads := memory_location' -> option call_stack.

Definition lock := location -> lockstate.
Definition state := threads * heap * lock * mVect.

Definition next_line : line -> line := S.

Ltac Ccase x x' := destruct (eq_mcontext x x');intros.

Definition eq_mc: forall x y : method*mcontext, {x=y}+{x<>y} :=
    eq_pair eq_method eq_mcontext.

Ltac MCcase x x' := destruct (eq_mc x x');intros.

Ltac Flcase x x' := destruct (eq_flow x x'); intros.

(* Definition of labels *)
(*************************************************)
Definition PPT := method * line * mcontext.

Definition eq_ppt : forall x y : PPT, {x=y}+{x<>y} :=
    eq_pair (eq_pair eq_method eq_line) eq_mcontext.

(* lVect *)
(**********************************************************************)
Definition incr_lVect (pi:lVect) (m:method) (c:mcontext) (fl:flow) :lVect
  :=  LVect.upd pi (m,c,fl) (S (LVect.get pi (m,c,fl))).

Definition incr_mVect (om:mVect) (m:method) (c:mcontext) : mVect :=
  MVect.upd om (m,c) (S (MVect.get om (m,c))).

Definition event := event_kind * PPT * field.
Definition action := option (memory_location' * event * memory_location).
(*************************************************)
(* Lock *)
(*************************************************)
Definition acquire (o:location) (o':location)
  (mu:lock) (mu':lock) : Prop :=
  (forall o'', o''<>o' -> mu'(o'')=mu(o'')) /\
  ((mu(o')=Free /\ mu'(o')=Held o 1) \/ 
    (exists n, mu(o')=Held o n /\ mu'(o')=Held o (S n))).

Definition release (o:location) (o':location)
  (mu:lock) (mu':lock) : Prop :=
  (forall o'', o''<>o' -> mu'(o'')=mu(o'')) /\
  ((mu(o')=Held o 1 /\ mu'(o')=Free) \/ 
    (exists n, mu(o')=Held o (S (S n)) /\ mu'(o')=Held o (S n))).

(*************************************************)
Definition local_of_list (this:val) (l:list val) :=
  fun x => 
    match x with
      | 0 => this
      | _ => if le_gt_dec x (length l) then nth (length l - x) l Null else Null
    end.

Definition invoke_mVect (om:mVect) (m:method) (c:mcontext) (omg:mVect) :=
  MVect.upd om (m,c) (S (MVect.get omg (m,c))).
Definition invoke_lVect (pi:lVect) (m:method) (c:mcontext) :=
  LVect.clear (fun mcfl => if eq_mc (fst mcfl) (m,c) then true else false) pi.
(*************************************************)

Definition fresh (sigma:heap) (a:location) : Prop :=
  forall p, not (inDom (a,p) sigma).

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
  | step1_ctx : forall c e i i' instr m o om 
    pi pi' rho rho' s s' sigma sigma'  
    (HYP1 : m.(body) i = Some instr)
    (HYP2: step0 o (m,i,c) instr (i,s,rho,sigma) (i',s',rho',sigma') e)
    (HYP3: pi'=incr_lVect pi m c (i,i')),
    step1 o ((CP m i c om pi,s,rho),sigma) 
    ((CP m i' c om pi',s',rho'),sigma') e
  | step1_new : forall a c cid i m o o' om pi pi' rho s sigma sigma'
    (HYP1 : m.(body) i = Some (New cid))
    (HYP2 : fresh sigma a)
    (HYP3 : o'=(a,(CP m i c om pi)))
    (HYP4 : pi'=incr_lVect pi m c (i,next_line i))
    (HYP5 : alloc sigma o' sigma'),
    step1 o ((CP m i c om pi,s),rho,sigma) 
    ((CP m (next_line i) c om pi',(Loc o')::s,rho),sigma') None.
  
  Inductive step2 :
    memory_location' -> (call_stack * heap * mVect) -> 
    (call_stack * heap * mVect) -> action -> Prop :=
  | step2_ctx : forall e cs fr fr' o omg sigma sigma'
    (H:step1 o (fr,sigma) (fr',sigma') e), 
    step2 o (fr::cs,sigma,omg) (fr'::cs,sigma',omg) e
  | step2_invoke : forall m i mid args rtype s s' v_list
    a0 m0 i0 c0 om0 pi0 m1 c1 om1 pi1 rho1 omg omg' om pi pi' c 
    rho cs' sigma o cId
    (H0 : m.(body) i = Some (InvokeVirtual (MethSign mid args rtype)))
    (H1 : s=v_list++(Loc (a0,CP m0 i0 c0 om0 pi0)::s'))
    (C0 : body m0 i0 = Some (New cId))
    (H2 : lookup p (MethSign mid args rtype) cId = Some m1)
    (H3 : c1=make_call_context m i c (make_new_context m0 i0 cId c0))
    (H4: om1 = invoke_mVect om m1 c1 omg)
    (H5: pi1 = invoke_lVect pi' m1 c1)  
    (H8: rho1=local_of_list (Loc (a0, CP m0 i0 c0 om0 pi0)) v_list)   
    (H10 : pi'=incr_lVect pi m c (i,S i))
    (H11 : omg' = incr_mVect omg m1 c1)
    (H12 : length v_list = length args),
    step2 o ((CP m i c om pi,s,rho)::cs',sigma,omg)  
    ((CP m1 0 c1 om1 pi1,nil,rho1)::
      (CP m (S i) c om pi',s',rho)::cs',sigma,omg') None
  | step2_return :
    forall o m i c om pi s rho cs sigma omg
      (H:m.(body) i = Some Return),
      step2 o ((CP m i c om pi,s,rho)::cs,sigma,omg) (cs,sigma,omg) None
  | step2_areturn : forall o m i c om pi v s rho s' rho' cs sigma omg p
    (H:m.(body) i = Some AReturn),
    step2 o ((CP m i c om pi,v::s,rho)::(p,s',rho')::cs,sigma,omg) 
    ((p,v::s',rho')::cs,sigma,omg) None.
  
  Definition upd_thread (L:threads) (o:memory_location') (cs:call_stack) : threads :=
    fun o' =>
      if eq_memloc' o o' then Some cs else L o'.

  Inductive step3 : threads -> (memory_location'*call_stack*heap*lock*mVect) ->
    (threads*heap*lock*mVect) -> action -> Prop :=
  | step3_ctx : forall L cs o sigma mu omg cs' sigma' omg' e
    (H:step2 o (cs,sigma,omg) (cs',sigma',omg') e),
    step3 L (o,cs,sigma,mu,omg) (upd_thread L o cs',sigma',mu,omg') e
  | step3_start : forall m i s a0 m0 i0 c0 om0 pi0 s' m1
    c1 om1 rho1 pi' L sigma lock omg c om pi rho cs o pi1 o' cId
    (H0 : m.(body) i = Some Run)
    (H1 : s=(Loc o')::s')
    (HO : o'=(a0,CP m0 i0 c0 om0 pi0))
    (C0 : body m0 i0 = Some (New cId))
    (H2 : lookup p (run) cId = Some m1)
    (H3 : c1=make_call_context m i c (make_new_context m0 i0 cId c0))
    (H4 : om1 = invoke_mVect MVect.init m1 c1 omg)
    (H5 : pi1 = LVect.init)
    (H8 : rho1 = local_of_list (Loc o') nil)
    (H9 : pi'=incr_lVect pi m c (i,S i))
    (H10 : forall c, L (fst o',c) = None),
    step3 L (o,(CP m i c om pi,s,rho)::cs,sigma,lock,omg) 
            (upd_thread 
              (upd_thread L o ((CP m (next_line i) c om pi',s',rho)::cs))
              (fst o',Some (snd o')) ((CP m1 0 c1 om1 pi1,nil,rho1)::nil),sigma,lock,incr_mVect omg m1 c1) 
            None
  | step3_enter :
    forall L m i mu mu' (o:memory_location') (o':memory_location) c om pi pi' s rho cs sigma omg
      (H0 : m.(body) i = Some MonitorEnter)
      (H2 : acquire (fst o) (fst o') mu mu')
      (H3 : pi'=incr_lVect pi m c (i,S i)),
      step3 L (o,(CP m i c om pi, (Loc o')::s,rho)::cs,sigma,mu,omg)
           (upd_thread L o ((CP m (next_line i) c om pi',s,rho)::cs),sigma,mu',omg)
           None
  | step3_exit :
    forall L m i mu mu' o o' c om pi pi' s rho cs sigma omg
      (H0 : m.(body) i = Some MonitorExit)
      (H2 : release (fst o) (fst o') mu mu')
      (H3 : pi'=incr_lVect pi m c (i,S i)),
      step3 L (o,(CP m i c om pi, (Loc o')::s,rho)::cs,sigma,mu,omg)
              (upd_thread L o ((CP m (next_line i) c om pi',s,rho)::cs),sigma,mu',omg)
              None.

  Inductive step : (threads*heap*lock*mVect) -> (threads*heap*lock*mVect) -> action -> Prop :=
  | step_inter :
    forall L L' fr cs o sigma mu omg sigma' mu' omg' e
      (H:step3 L (o,fr::cs,sigma,mu,omg) (L',sigma',mu',omg') e)
      (H1:L o = Some (fr::cs)),
      step (L,sigma,mu,omg) (L',sigma',mu',omg') e.
End step.

Definition om_init (p:program) : mVect :=  MVect.upd MVect.init (p.(main),init_mcontext) 1.
Definition cp_init (p:program) := (CP p.(main) 0 init_mcontext (om_init p) LVect.init).

Definition om_run_address (p:program) : mVect :=  MVect.init.
Definition cp_run_address (p:program) := (CP p.(foo) 0 init_mcontext (om_run_address p) LVect.init).

Definition run_address := 1%positive.

Definition sigma_init (p:program) : heap := 
  (fun l' => if eq_memloc l' (run_address,cp_run_address p) then Some (fun f => Null) else None).

Definition threads_init (p:program) : threads :=
  fun l => 
    if eq_memloc' l (run_address, None) then 
      Some ((cp_init p,nil,(fun _ => Null))::nil) 
      else None.

Definition init (p:program) : state :=
  (threads_init p, sigma_init p, (fun _ => Free), om_init p).

Inductive reachable (p:program) : state -> Prop :=
| reachable_0 : reachable p (init p)
| reachable_next : 
  forall st st' e (H:reachable p st) (H':step p st st' e), reachable p st'.

Inductive reachable_h (p:program) : list heap -> state -> Prop :=
| reachable_h_0 : 
  reachable_h p (sigma_init p::nil) (init p)
| reachable_h_next : forall st L sigma mu omg e l,
  reachable_h p l st -> 
  step p st (L,sigma,mu,omg) e -> 
  reachable_h p (sigma::l) (L,sigma,mu,omg).

Inductive heap_reach (ls:list heap) : memory_location -> memory_location -> Prop :=
| heap_reach_root: forall sigma l
  (H0:In sigma ls)
  (H:inDom l sigma),
  heap_reach ls l l
| heap_reach_next : forall sigma l l' l'' m f
  (H':In sigma ls)
  (H:heap_reach ls l l')
  (H0:sigma l' = Some m)
  (H1:m f = Loc l''),
  heap_reach ls l l''.
 

(******** Data races *********)

  Inductive conflicting_actions : action -> action -> Prop :=
  | conflicting_actions_def : forall o1 o2 o' ppt1 ppt2 f k1 k2,
    o1<>o2 ->
    (k1=Put \/ k2=Put) ->
    conflicting_actions (Some (o1,(k2,ppt1,f),o')) (Some (o2,(k1,ppt2,f),o')).


Inductive Races (p:program) (st:state) (a1 a2:action) : Prop :=
  Races_def : forall st1 st2,
    reachable p st ->
    step p st st1 a1 ->
    step p st st2 a2 ->
    a1<>a2 ->
    conflicting_actions a1 a2 ->
    Races p st a1 a2.

Inductive get_ppt (ppt:PPT) : action -> Prop :=
| get_ppt_def : forall o f o' k, get_ppt ppt (Some (o,(k,ppt,f),o')).

Inductive get_owner (o:memory_location') : action -> Prop :=
| get_owner_def : forall ppt f o' k, get_owner o (Some (o,(k,ppt,f),o')).

Inductive get_target (o:memory_location) : action -> Prop :=
| get_target_def : forall o1 ppt f k, get_target o (Some (o1,(k,ppt,f),o)).


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

End CountingSemantic.

