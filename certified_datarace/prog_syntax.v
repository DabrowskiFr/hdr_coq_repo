Require Export ZArith.
Require Export List.
Require Export axioms.
Open Scope type_scope.

Definition var := nat.
Definition classId := positive.
Definition field := positive.
Definition methodId := positive.

Definition line := nat.

Record method_signature :Set := MethSign{
  ms_name : methodId;
  args : list classId;
  rtype : option classId
}.

Inductive instruction : Set :=
| AConstNull
| New (c:classId)
| ALoad (x:var)
| AStore (x:var)
| GetField (f:field)
| PutField (f:field)
| Ifnd (i:line)
| Goto (i:line)
| InvokeVirtual (ms:method_signature)
| AReturn
| Return
| MonitorEnter
| MonitorExit
| Run
.

Record method : Set := Meth{
  signature : method_signature;
  instr : list instruction    
}.

Definition body (m:method) : nat -> option instruction :=
  List.nth_error (instr m).

Record class : Set := Class{
  c_name : classId;
  fields : list field;
  methods : list method
}.

Definition flow := line * line.

Record program : Set := Prog{
  classes : list class;
  
  main_class : class;
  main_class_prop : In main_class classes;

  main : method;
  main_prop_1 : In main main_class.(methods);
  main_prop_2 : main.(signature).(args)=nil;
  main_prop_3 : main.(signature).(rtype)=None;
  main_prop_4 : main_class.(c_name) = 1%positive;

  foo : method;
  foo_prop : body foo 0 = Some (New main_class.(c_name));

  lookup : method_signature -> classId -> option method;
  lookup_prop_1 : forall ms cid m,
    lookup ms cid = Some m ->
    exists cl,
      In cl classes /\
      cl.(c_name) = cid /\
      In m cl.(methods) /\
      m.(signature)=ms;

  loop : method * line -> flow  
}.

Definition run : method_signature :=
  MethSign 1%positive nil None.

Inductive cflow : method -> flow -> Prop :=
| cflow_aconstnull : forall m i 
  (H:m.(body)(i)=Some AConstNull), cflow m (i,S i)
| cflow_new : forall m i cid
  (H:m.(body)(i)=Some (New cid)), cflow m (i,S i)
| cflow_aload : forall m i x 
  (H:m.(body)(i)=Some (ALoad x)), cflow m (i,S i)
| cflow_astore : forall m i x 
  (H:m.(body)(i)=Some (AStore x)), cflow m (i,S i)
| cflow_getfield : forall m i f
  (H:m.(body)(i)=Some (GetField f)), cflow m (i,S i)
| cflow_putfield : forall m i f
  (H:m.(body)(i)=Some (PutField f)), cflow m (i,S i)
| cflow_ifndl : forall m i j 
  (H:m.(body)(i)=Some (Ifnd j)), cflow m (i,S i)
| cflow_ifndr : forall m i j 
  (H:m.(body)(i)=Some (Ifnd j)), cflow m (i,j)
| cflow_goto : forall m i j
  (H:m.(body)(i)=Some (Goto j)), cflow m (i,j)
| cflow_invoke : forall m i sig
  (H:m.(body)(i)=Some (InvokeVirtual sig)), cflow m (i,S i)
| cflow_start : forall m i 
    (H:m.(body)(i)=Some Run), cflow m (i,S i)
| cflow_monitorenter : forall m i 
  (H:m.(body)(i)=Some MonitorEnter), cflow m (i,S i)
| cflow_exit : forall m i 
  (H:m.(body)(i)=Some MonitorExit), cflow m (i,S i).

Inductive leads_to : nat -> nat -> list nat -> method -> Prop :=
| leads_to1 : forall i j m 
  (H:cflow m (i,j)),  leads_to i j (i::j::nil) m
| leads_to2 : forall i j k l m
  (H:cflow m (i,k)) 
  (H':leads_to k j (l) m),  leads_to i j (i::l) m.

Definition safe_loop (p:program) : Prop :=
  forall (cl:class) (m:method) (l:list nat) (i:line) (cid:classId),
    In cl p.(classes) ->
    In m cl.(methods) ->
    (m.(body) i = Some (New cid)) ->
    (leads_to i i (i::l) m) ->
    exists k, exists ik, exists jk, 
      nth_error l k = value ik  /\ nth_error l (S k) = value jk /\ ((ik,jk) = 
        p.(loop) (m,i)).






