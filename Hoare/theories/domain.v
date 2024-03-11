    Require Import Coq.Arith.EqNat.

    Lemma nat_eqdec : forall x y : nat, {x = y} + {x <> y}.
    Proof.
        intros x y.
        destruct (eq_nat_decide x y) as [ Ha | Ha ].
        -   left.
            exact (eq_nat_eq x y Ha).
        -   right.
            contradict Ha.
            exact (eq_eq_nat x y Ha).
    Qed.

    Module D : Domain.

    Definition var := nat.
    
    Inductive aexpr' : Set := 
        | Var : var -> aexpr' 
        | Const : nat -> aexpr'.
    
    Definition aexpr := aexpr'.
    
    Inductive bexpr' : Set := 
        | BTrue : bexpr'
        | BFalse : bexpr' 
        | BAnd : bexpr' -> bexpr' -> bexpr'.

    Definition bexpr := bexpr'.

    Definition value := nat.

    Definition store := nat -> value.    

    Definition update (σ : store) (x : var) (v : value) (y : var) :=
        if nat_eqdec x y then v else σ y.

    Definition evalAExpr (a : aexpr) (σ : store) : value :=
        match a with 
            | Var x => σ x
            | Const n => n 
        end.

    Fixpoint evalBExpr (b : bexpr) (σ : store) : Prop :=
        match b with 
            | BTrue => True 
            | BFalse => False 
            | BAnd b1 b2 => 
                (evalBExpr b1 σ) /\ (evalBExpr b2 σ)
        end.

    Lemma evalBExpr_dec : forall b σ, evalBExpr b σ \/ ~ evalBExpr b σ.
    Proof.
        intros b σ.
        induction b as [ | | b1 IHb1 b2 IHb2 ].
        -   simpl.
            left.
            exact I.
        -   right.
            intro.
            assumption.
        -   destruct IHb1 as [Ha | Ha], IHb2 as [ Hb | Hb ].
            +   left.
                split.
                    *   exact Ha.
                    *   exact Hb.
            +   right.
                contradict Hb.
                destruct Hb.
                assumption.
            +   firstorder.
            +   firstorder.   
    Qed.

End D.