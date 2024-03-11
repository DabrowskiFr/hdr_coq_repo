Require Export prog_syntax.

Lemma eq_var : forall x1 x2: var, {x1=x2}+{x1<>x2}.
Proof.
  decide equality.
Qed.

Lemma eq_pos : forall p1 p2: positive, {p1=p2}+{p1<>p2}.
Proof.
  decide equality.
Qed.

Lemma eq_line : forall i1 i2: line, {i1=i2}+{i1<>i2}.
Proof.
  decide equality.
Qed.

Lemma eq_flow : forall i1 i2: line*line, {i1=i2}+{i1<>i2}.
Proof.
  decide equality.
  apply eq_line.
  apply eq_line.
Qed.

Lemma eq_method_signature : forall ms1 ms2: method_signature,
  {ms1=ms2}+{ms1<>ms2}.
Proof.
  repeat decide equality.
Qed.

Lemma eq_instruction : forall i1 i2: instruction, {i1=i2}+{i1<>i2}.
Proof.
  repeat decide equality.
Qed.

Lemma eq_method : forall m1 m2: method, {m1=m2}+{m1<>m2}.
Proof.
  decide equality.
  decide equality.
  apply eq_instruction.
  apply eq_method_signature.
Qed.

Lemma eq_class : forall c1 c2: class, {c1=c2}+{c1<>c2}.
Proof.
  decide equality.
  decide equality.
  apply eq_method.
  decide equality.
  decide equality.
  decide equality.
Qed.

Ltac comp x y :=
  match type of x with
    | method => 
      match type of y with
        | method => destruct (eq_method x y)
        | _ => fail
      end
    | method_signature => 
      match type of y with
        | method_signature => destruct (eq_method_signature x y)
        | _ => fail
      end
    | var => 
      match type of y with
        | var => destruct (eq_var x y)
        | _ => fail
      end
    | field => 
      match type of y with
        | field => destruct (eq_pos x y)
        | _ => fail
      end
    | classId => 
      match type of y with
        | classId => destruct (eq_pos x y)
        | _ => fail
      end
    | _  => fail
  end; [subst|idtac].

Section pair_eq.

  Variable A B : Set.
  Variable eq_A : forall x y : A, {x=y}+{x<>y}.
  Variable eq_B : forall x y : B, {x=y}+{x<>y}.

  Lemma eq_pair : forall x y : A*B, {x=y}+{x<>y}.
  Proof.
    decide equality.
  Qed.

  Lemma eq_some : forall x y : option A, {x=y}+{x<>y}.
  Proof.
    decide equality.
  Qed.

End pair_eq.

Implicit Arguments eq_pair [A B].
Implicit Arguments eq_some [A].

Definition in_list := In_dec eq_line.

