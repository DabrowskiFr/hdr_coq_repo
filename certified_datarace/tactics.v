Ltac inv H := inversion H; try (subst;clear H).
Ltac inj H := injection H; intros; try (subst;clear H).
Ltac dup H H' := generalize H; intro H'.