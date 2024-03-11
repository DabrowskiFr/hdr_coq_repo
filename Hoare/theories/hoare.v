
Require Import Coq.Program.Equality.

Module Type Domain.

    Parameter var : Set.
    Parameter aexpr : Set.
    Parameter bexpr : Set.
    Parameter value : Set.
    Parameter store : Set.
    Parameter update : store -> var -> value -> store.
    Parameter evalAExpr : aexpr -> store -> value.
    Parameter evalBExpr : bexpr -> store -> Prop.
    Parameter evalBExpr_dec : 
        forall b σ, evalBExpr b σ \/ ~ evalBExpr b σ.

End Domain. 

Module Syntax (Import D : Domain).

    Inductive command : Set :=
    | Skip : command 
    | Assign : var -> aexpr -> command 
    | Seq : command -> command -> command 
    | If : bexpr -> command -> command -> command
    | While : bexpr -> command -> command.

End Syntax.

Module Hoare (Import D : Domain).

    Module Import S := Syntax (D).

    Inductive command : Set :=
        | Skip : command 
        | Assign : var -> aexpr -> command 
        | Seq : command -> command -> command 
        | If : bexpr -> command -> command -> command
        | While : bexpr -> command -> command.

    Inductive bigstep : command * store -> store -> Prop :=
        | bigstep_Skip : forall σ, bigstep (Skip, σ) σ
        | bigstep_Assign : forall x e σ,
            bigstep (Assign x e, σ) (update σ x (evalAExpr e σ))
        | bigstep_Seq : forall c1 c2 σ σ' σ'',
            bigstep (c1, σ) σ'' ->
            bigstep (c2, σ'') σ' -> 
            bigstep (Seq c1 c2, σ) σ'
        | bigstep_If_t : forall b c1 c2 σ σ',
            evalBExpr b σ -> 
            bigstep (c1,σ) σ' ->
            bigstep (If b c1 c2, σ) σ' 
        | bigstep_If_f : forall b c1 c2 σ σ',
            ~ (evalBExpr b σ) -> 
            bigstep (c2,σ) σ' ->
            bigstep (If b c1 c2, σ) σ' 
        | bigstep_While_t : forall b c σ σ' σ'',
            evalBExpr b σ ->
            bigstep (c, σ) σ'' ->
            bigstep (While b c, σ'') σ' ->
            bigstep (While b c, σ) σ'
        | bigstep_While_f : forall b c σ,
            ~ evalBExpr b σ ->
            bigstep (While b c, σ) σ.

    Definition assertion := store -> Prop.

    Definition substitution (p : assertion) (x : var) (e : aexpr) : assertion :=
        fun σ => p (update σ x (evalAExpr e σ)).

    Inductive proof : assertion -> command -> assertion -> Prop :=
        | proof_Skip : forall p, proof p Skip p 
        | proof_Assign : forall x e p, 
            proof (substitution p x e) (Assign x e) p
        | proof_Seq : forall c1 c2 p q r,
            proof p c1 q ->
            proof q c2 r -> 
            proof p (Seq c1 c2) r
        | proof_If : forall b c1 c2 p q,
            proof (fun σ => evalBExpr b σ /\ p σ ) c1 q ->
            proof (fun σ => ~ evalBExpr b σ /\ p σ) c2 q ->
            proof p (If b c1 c2) q
        | proof_While : forall b c p,
            proof (fun σ => evalBExpr b σ /\ p σ ) c p ->
            proof p (While b c) (fun σ => ~evalBExpr b σ /\ p σ)
        | proof_Imp : forall c p q p' q',
            proof p' c q' -> 
            (forall σ, p σ -> p' σ) ->
            (forall σ, q' σ -> q σ) ->
            proof p c q.

    (* proof -> proof *)

    Definition valid (p : assertion) (c : command) (q : assertion) : Prop :=
        forall σ σ', bigstep (c, σ) σ' -> p σ -> q σ'.

    Theorem correctness : 
        forall p c q, proof p c q -> valid p c q.
    Proof.
        intros p c q proof.
        induction proof.
        -   intros σ σ' H_bigstep H_p.
            inversion H_bigstep; subst.
            exact H_p.
        -   intros σ σ' H_bigstep H_p.
            inversion H_bigstep; subst.
            exact H_p.
        -   intros σ σ' H_bigstep H_p.
            inversion H_bigstep; subst.
            assert (q σ'') as H_q by
                exact (IHproof1 σ σ'' H3 H_p).
            exact (IHproof2 σ'' σ' H4 H_q).
        -   intros σ σ' H_bigstep H_p.
            inversion H_bigstep; subst.
            exact (IHproof1 σ σ' H5 (conj H4 H_p)).
            exact (IHproof2 σ σ' H5 (conj H4 H_p)).
        -   intros σ σ' H_bigstep H_p.
            dependent induction H_bigstep.
            + assert (p σ'') as H_p' by
                exact (IHproof _ _ H_bigstep1 (conj H H_p)).
            exact (IHH_bigstep2 _ _ proof0 IHproof _ (refl_equal _) H_p'). 
            + exact (conj H H_p).
        -   intros σ σ' H_bigstep H_p.  
            exact (H0 σ' (IHproof σ σ' H_bigstep (H σ H_p))). 
    Qed.

    Definition wlp ( c : command) (q : assertion) : assertion :=
        fun σ => forall σ', bigstep (c, σ) σ' -> q σ'.

    Notation "A ∩ B" := (fun σ =>  A σ /\ B σ) (at level 79).
    Notation "A ∪ B" := (fun σ =>  A σ \/ B σ) (at level 80).
    Notation "A ⊑ B" := (forall σ, A σ -> B σ) (at level 81).
    Notation "! A" := (fun σ => ~ A σ) (at level 78).

    Hint Unfold substitution wlp : hoare.

    Lemma wlp_Skip : forall q, wlp Skip q ⊑ q.
    Proof.
        eauto using bigstep with hoare.
    Qed.

    Lemma wlp_Assign : forall x e q, wlp (Assign x e) q ⊑ substitution q x e.
        eauto using bigstep with hoare.
    Qed.

    Lemma wlp_Seq : 
        forall c1 c2 q, wlp (Seq c1 c2) q ⊑ wlp c1 (wlp c2 q).
    Proof.
        eauto using bigstep with hoare.
    Qed.

    Lemma wlp_If : forall b c1 c2 q σ, 
        wlp (If b c1 c2) q σ ->
        ((evalBExpr b ∩ wlp c1 q) ∪ (! evalBExpr b ∩ wlp c2 q)) σ.
    Proof.
        unfold wlp.
        intros b c1 c2 q σ Ha.
        case_eq (evalBExpr_dec b σ); eauto using bigstep.
    Qed.

    Lemma wlp_While_1 : forall b c q σ,
        evalBExpr b σ -> wlp (While b c) q σ  ->
        wlp c (wlp (While b c) q) σ.
    Proof.
        unfold wlp.
        eauto using bigstep with hoare.
    Qed.

    Lemma wlp_While_2 : forall b c q σ,
    ~ evalBExpr b σ -> wlp (While b c) q σ  -> q σ.
    Proof.
        unfold wlp.
        eauto using bigstep with hoare.
    Qed.

    Lemma valid_wlp : forall p c q,
        valid p c q -> forall σ, p σ -> wlp c q σ.
    Proof.
        unfold valid, wlp; eauto.
    Qed.

    Proposition wp_prop : forall c q, proof (wlp c q) c q.
    Proof.
        induction c.
        -   intros q.
            apply (proof_Imp Skip _ q q q).
            apply proof_Skip.
            unfold wlp.
            intros.
            apply H.
            constructor.
            trivial.
        -   intros q.
            apply (proof_Imp _ _ q (substitution q v a) q).
            constructor.
            unfold wlp.
            intros.
            apply H.
            constructor.
            trivial.
        -   intros q.
            apply (proof_Imp _ _ _ (wlp c1 (wlp c2 q)) q).
            +   exact (proof_Seq _ _ _ _ _ (IHc1 _) (IHc2 _)).
            +   apply wlp_Seq.
            +   trivial.
        -   intros q.
            constructor.
            +   eapply proof_Imp.
                apply IHc1.
                intros.
                destruct H.
                apply wlp_If in H0.
                destruct H0.
                destruct H0.
                apply H1.
                destruct H0.
                elim H0.
                assumption.
                trivial.
            +   eapply proof_Imp.
                apply IHc2.
                intros.
                destruct H.
                apply wlp_If in H0.
                destruct H0.
                destruct H0.
                elim H.
                assumption.
                destruct H0.
                apply H1.
                trivial.
        -   intros q.
            assert (proof (wlp c (wlp (While b c) q)) c (wlp (While b c) q))
                by exact (IHc (wlp (While b c) q)).
            assert (proof (evalBExpr b ∩ wlp (While b c) q) c (wlp (While b c) q)) as Hu.
            {
                eapply proof_Imp.
                - apply H.
                - intros σ [Ha Hb].
                    eapply wlp_While_1; auto.
                - trivial. 
            }
            assert (proof (wlp (While b c) q) (While b c) (! evalBExpr b ∩ wlp (While b c) q)).
            {
                apply proof_While.
                apply Hu.
            }
            apply (proof_Imp _ _ _ _ _ H0).
            trivial.
            intros σ [Ha Hb].
            eapply wlp_While_2; eauto.
    Qed.

    Lemma refl : forall (q : assertion), q ⊑ q.
    Proof.
        trivial.
    Qed.
    
    Theorem completness : forall c p q, valid p c q -> proof p c q.
    Proof.
        intros c p q H_valid.
        assert (proof (wlp c q) c q) as Ha 
            by apply wp_prop.
        assert (p ⊑ wlp c q) as Hb
            by exact (valid_wlp _ _ _ H_valid).
        exact (proof_Imp c p q (wlp c q) q Ha Hb (refl q)).
    Qed.

End Hoare.

