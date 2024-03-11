Require Export sem.

Module ObjectSensitivity <: CONTEXT.

  Definition site := method * line.
  Definition mcontext : Set := list site.
  Definition pcontext : Set := list site.
  Definition make_new_context : method -> line -> classId -> mcontext -> pcontext :=
    fun m l _ c => (m,l)::c.
  Definition make_call_context : method -> line -> mcontext -> pcontext -> mcontext :=
    fun _ _ _ c => c.
  Definition init_mcontext : mcontext := nil.
  Definition init_pcontext : pcontext := nil.
  Definition get_class (p:program) (c:pcontext) : option classId :=
    match c with
      | nil => Some (c_name (main_class p))
      | (m,i)::_  =>
        match body m i with
          | Some (New cid) => Some cid
          | _ => None
        end
    end.

  Lemma class_make_new_context : forall p m i cid c,
    body m i = Some (New cid) ->
    get_class p (make_new_context m i cid c) = Some cid.
  Proof.
    unfold get_class, make_new_context; intros.
    rewrite H; auto.
  Qed.

  Lemma class_init_pcontext : forall p,
    get_class p init_pcontext = Some p.(main_class).(c_name).
  Proof.
    intros; simpl.
    auto.
  Qed.

  Lemma eq_pcontext : forall c1 c2:pcontext, {c1=c2}+{c1<>c2}.
  Proof.
    repeat decide equality.
  Qed.

  Definition eq_mcontext : forall c1 c2:mcontext, {c1=c2}+{c1<>c2} := eq_pcontext.

End ObjectSensitivity.

Module PointsToSemantic := MakeSemantic ObjectSensitivity.


