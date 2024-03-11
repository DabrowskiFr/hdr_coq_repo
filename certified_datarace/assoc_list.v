Require Export List.

Module Type ASSOC_DOMAIN.

  Parameter domain codomain : Set.
  Parameter eq_domain : forall x y:domain, {x=y}+{x<>y}.
  Parameter eq_codomain : forall x y:codomain, {x=y}+{x<>y}.

  Parameter def : codomain. 

End ASSOC_DOMAIN.

Module Type ASSOC.

  Parameter A B t : Set.

  Parameter default : B.
  Parameter get : t -> A -> B.
  Parameter upd : t -> A -> B -> t.
  Parameter clear : (A->bool) -> t -> t.
  Parameter init : t.
  Parameter get_upd1 : forall l x b, get (upd l x b) x = b.
  Parameter get_upd2 : forall l x b y, x<>y -> get (upd l x b) y = get l y.
  Parameter get_clear : forall f l x, get (clear f l) x = if f x then default else get l x.
  Parameter get_init : forall x, get init x = default.
  Parameter eq : forall x y:t, {x=y}+{x<>y}.

End ASSOC.

Module AssocList (K:ASSOC_DOMAIN) : ASSOC 
  with Definition A := K.domain
  with Definition B := K.codomain
  with Definition default := K.def.

  Import K.

  Definition A := domain.
  Definition B := codomain.
  Definition t := list (A*B).

  Definition default := def.

  Fixpoint get (l:list (A*B)) (x0:A) : B :=
    match l with
      | nil => def
      | (x,b)::q => if eq_domain x0 x then b else get q x0
    end.

  Definition upd (l:t) (x0:A) (b0:B) : t := (x0,b0)::l.

  Lemma get_upd1 : forall l x b, get (upd l x b) x = b.
  Proof.
    unfold upd; intros; simpl.
    destruct (eq_domain x x); intuition.
  Qed.

  Lemma get_upd2 : forall l x b y, x<>y -> get (upd l x b) y = get l y.
  Proof.
    unfold upd; intros; simpl.
    destruct (eq_domain y x); intuition.
    elim H; auto.
  Qed.

  Lemma eq : forall x y:t, {x=y}+{x<>y}.
  Proof.
    decide equality.
    decide equality.
    apply eq_codomain.
    apply eq_domain.
  Qed.

  Fixpoint clear (f:A->bool) (l:list (A*B)) : t :=
    match l with
      | nil => nil
      | (x,b)::q => if f x then clear f q else (x,b)::(clear f q)
    end.

  Lemma get_clear : forall f l x, get (clear f l) x = if f x then default else get l x.
  Proof.
    induction l; simpl; intros.
    destruct (f x); auto.
    destruct a as [x0 b0].
    destruct (eq_domain x x0); subst.
    case_eq (f x0); intros; auto.
    rewrite IHl; rewrite H; auto.
    simpl.
    destruct (eq_domain x0 x0); intuition.
    case_eq (f x0); intros; auto.
    simpl.
    destruct (eq_domain x x0); intuition.
  Qed.

  Definition init : t := nil.
  Lemma get_init : forall x, get init x = default.
  Proof.
    intuition.
  Qed.

End AssocList.