Require Export sem.

Module Standard <: CONTEXT.
  
  (* Inductive unit : Set :=  tt : unit *)
  Definition mcontext : Set := unit.
  Definition pcontext : Set := classId.

  Definition make_new_context : method -> line -> classId -> mcontext -> pcontext :=
    fun m l cid c => cid.
  Definition make_call_context : method -> line -> mcontext -> pcontext -> mcontext :=
    fun _ _ _ _ => tt.

  Definition init_mcontext : mcontext := tt.
  Definition init_pcontext : pcontext := 1%positive.
  Definition get_class (p:program) (c:pcontext) : option classId := Some c.

  Lemma class_make_new_context : forall p m i cid c,
    body m i = Some (New cid) ->
    get_class p (make_new_context m i cid c) = Some cid.
  Proof.
    intros; reflexivity.
  Qed.

  Lemma class_init_pcontext : forall p,
    get_class p init_pcontext = Some p.(main_class).(c_name).
  Proof.
    intros; rewrite main_prop_4; auto.
  Qed.

  Definition eq_pcontext : forall c1 c2:pcontext, {c1=c2}+{c1<>c2} := eq_pos.
  Definition eq_mcontext : forall c1 c2:mcontext, {c1=c2}+{c1<>c2}. 
  Proof. decide equality. Qed.

End Standard.

Module StandardSemantic := MakeSemantic Standard.

Require Import sem_equiv.

Module Standard_equiv (S:SEMANTIC).

Module I := SemEquivProp StandardSemantic S.

Lemma race_equiv : 
  forall p ppt ppt',
    StandardSemantic.race_without_context p ppt ppt' -> S.race_without_context p ppt ppt'.
Proof.
  intros p ppt ppt'.
  set (pequiv:=fun (p1:classId) (p2:S.C.pcontext) => 
    S.C.get_class p p2 = Some p1).
  set (mequiv:=fun (p1:unit) (p2:S.C.mcontext) => True).
  apply (I.race_equiv p pequiv mequiv); simpl; unfold pequiv, mequiv; intros; auto.
  rewrite S.C.class_init_pcontext.
  rewrite main_prop_4.
  reflexivity.
  inv H; inv H0; congruence.
  rewrite S.C.class_make_new_context.
  reflexivity.
  auto.
Qed.

End Standard_equiv.




