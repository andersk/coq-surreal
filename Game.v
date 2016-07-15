Require Import
        Coq.Program.Basics
        Coq.Setoids.Setoid
        Coq.Structures.Orders.

Delimit Scope Game_scope with Game.
Local Open Scope Game_scope.

Inductive Game :=
  {
    Left : Type;
    lefts : Left -> Game;
    Right : Type;
    rights : Right -> Game
  }.

Module Game <: EqLtLe <: StrOrder.

  Definition t := Game.

  Fixpoint le (x : Game) :=
    fix le_x (y : Game) : Prop :=
      (forall xLi,
          (exists yLi, lefts x xLi <= lefts y yLi) \/
          (exists xLRi, rights (lefts x xLi) xLRi <= y)) /\
      (forall yRi,
          (exists yRLi, le_x (lefts (rights y yRi) yRLi)) \/
          (exists xRi, rights x xRi <= rights y yRi))
  where "x <= y" := (le x y) : Game_scope.

  Definition nle (y x : Game) : Prop :=
    (exists yLi, x <= lefts y yLi) \/
    (exists xRi, rights x xRi <= y).

  Infix "!<=" := nle (at level 70, no associativity) : Game_scope.

  Definition eq (x y : Game) : Prop := x <= y /\ y <= x.

  Infix "==" := eq (at level 70, no associativity) : Game_scope.

  Definition lt (x y : Game) : Prop := x <= y /\ y !<= x.

  Infix "<" := lt.

  Theorem le_step (x y : Game) :
    x <= y <->
    (forall xLi, y !<= lefts x xLi) /\
    (forall yRi, rights y yRi !<= x).
  Proof.
    destruct x.
    destruct y.
    reflexivity.
  Qed.

  Theorem le_refl (x : Game) : x <= x.
  Proof.
    induction x; (split; [left | right]; eauto).
  Qed.

  Theorem nle_irrefl (x : Game) : ~ x !<= x.
  Proof.
    induction x as [XLeft xLefts IHxLefts XRight xRights IHxRights].
    destruct 1 as [[xLi LExxL] | [xRi LExRx]].
    - apply IHxLefts with xLi.
      apply le_step in LExxL.
      apply LExxL.
    - apply IHxRights with xRi.
      apply le_step in LExRx.
      apply LExRx.
  Qed.

  Lemma le_trans' (x y z : Game) :
    (x <= y -> y <= z -> x <= z) /\
    (y !<= x -> y <= z -> z !<= x) /\
    (x <= y -> z !<= y -> z !<= x).
  Proof.
    revert x y z.
    fix le_trans' 1.
    intro x.
    fix le_trans'_x 1.
    intro y.
    fix le_trans'_x_y 1.
    intro z.
    split; [| split].
    - intros LExy LEyz.
      apply le_step.
      split.
      + intro xLi.
        destruct le_trans' with (lefts x xLi) y z as (_ & IH & _).
        apply IH.
        * apply le_step.
          assumption.
        * assumption.
      + intro zRi.
        destruct le_trans'_x_y with (rights z zRi) as (_ & _ & IH).
        apply IH.
        * assumption.
        * apply le_step.
          assumption.
    - intros [[yLi LExyL] | [xRi LExRy]] LEyz.
      + destruct le_trans'_x with (lefts y yLi) z as (_ & _ & IH).
        apply IH.
        * assumption.
        * apply le_step.
          assumption.
      + right.
        eexists.
        destruct le_trans' with (rights x xRi) y z as (IH & _ & _).
        apply IH; assumption.
    - intros LExy [[zLi LEyzL] | [yRi LEyRz]].
      + left.
        eexists.
        destruct le_trans'_x_y with (lefts z zLi) as (IH & _ & _).
        apply IH; assumption.
      + destruct le_trans'_x with (rights y yRi) z as (_ & IH & _).
        apply IH.
        * apply le_step.
          assumption.
        * assumption.
  Qed.

  Theorem le_trans (x y z : Game) : x <= y -> y <= z -> x <= z.
  Proof.
    apply le_trans'.
  Qed.

  Theorem nle_le_trans (x y z : Game) : y !<= x -> y <= z -> z !<= x.
  Proof.
    apply le_trans'.
  Qed.

  Theorem le_nle_trans (x y z : Game) : x <= y -> z !<= y -> z !<= x.
  Proof.
    apply le_trans'.
  Qed.

  Theorem le_not_nle (x y : Game) :
    x <= y -> ~ x !<= y.
  Proof.
    intros ? ?.
    eapply nle_irrefl, nle_le_trans; eassumption.
  Qed.

  Add Relation Game le
      reflexivity proved by le_refl
      transitivity proved by le_trans
        as le_relation.

  Add Relation Game nle
    as nle_relation.

  Add Morphism le with signature le --> le ++> impl as le_le_compat.
  Proof.
    unfold impl.
    eauto using le_trans.
  Qed.

  Add Morphism nle with signature le ++> le --> impl as nle_le_compat.
  Proof.
    unfold impl.
    eauto using nle_le_trans, le_nle_trans.
  Qed.

  Theorem eq_refl (x : Game) : x == x.
  Proof.
    split; reflexivity.
  Qed.

  Theorem eq_sym (x y : Game) : x == y -> y == x.
  Proof.
    destruct 1; split; assumption.
  Qed.

  Theorem eq_trans (x y z : Game) : x == y -> y == z -> x == z.
  Proof.
    destruct 1, 1.
    split; etransitivity; eassumption.
  Qed.

  Add Relation Game eq
      reflexivity proved by eq_refl
      symmetry proved by eq_sym
      transitivity proved by eq_trans
        as eq_relation.

  Add Morphism le with signature eq ==> eq ==> iff as le_compat.
  Proof.
    unfold impl.
    intros ? ? [? ?] ? ? [? ?].
    split; eauto using le_trans.
  Qed.

  Add Morphism nle with signature eq ==> eq ==> iff as nle_compat.
  Proof.
    unfold impl.
    intros ? ? [? ?] ? ? [? ?].
    split; eauto using nle_le_trans, le_nle_trans.
  Qed.

  Theorem eq_equiv : Equivalence eq.
  Proof.
    split.
    - exact eq_refl.
    - exact eq_sym.
    - exact eq_trans.
  Qed.

  Theorem lt_irrefl (x : Game) : ~ x < x.
  Proof.
    intros [LExx NLExx].
    contradict NLExx.
    apply nle_irrefl.
  Qed.

  Theorem le_lt_trans (x y z : Game) : x <= y -> y < z -> x < z.
  Proof.
    destruct 2.
    split.
    - eapply le_trans; eassumption.
    - eapply le_nle_trans; eassumption.
  Qed.

  Theorem lt_le_trans (x y z : Game) : x < y -> y <= z -> x < z.
  Proof.
    destruct 1.
    split.
    - eapply le_trans; eassumption.
    - eapply nle_le_trans; eassumption.
  Qed.

  Theorem lt_trans (x y z : Game) : x < y -> y < z -> x < z.
  Proof.
    destruct 1.
    apply le_lt_trans.
    assumption.
  Qed.

  Theorem lt_strorder : StrictOrder lt.
  Proof.
    split.
    - exact lt_irrefl.
    - exact lt_trans.
  Qed.

  Add Relation Game lt
      transitivity proved by lt_trans as lt_relation.

  Add Morphism lt with signature (eq ==> eq ==> iff) as lt_compat.
  Proof.
    intros x y Exy z w Ezw.
    split.
    - intros [LExz NLEzx].
      split; rewrite <- Exy, <- Ezw; assumption.
    - intros [LEyw NLEwy].
      split; rewrite Exy, Ezw; assumption.
  Qed.

  Fixpoint opp (x : Game) : Game :=
    {|
      lefts xRi := -rights x xRi;
      rights xLi := -lefts x xLi
    |}
  where "- x" := (opp x) : Game_scope.

  Theorem opp_step (x : Game) :
    -x = {|
      lefts xRi := -rights x xRi;
      rights xLi := -lefts x xLi
    |}.
  Proof.
    destruct x.
    reflexivity.
  Qed.

  Theorem opp_opp (x : Game) : -(-x) == x.
  Proof.
    split; induction x; (split; [left | right]; eauto).
  Qed.

  Lemma opp_le' (x y : Game) :
    (x <= y -> -y <= -x) /\
    (y !<= x -> -x !<= -y).
  Proof.
    revert x y.
    fix opp_le' 1.
    intro x.
    fix opp_le'_x 1.
    intro y.
    split.
    - intros.
      apply le_step.
      apply le_step in H.
      split.
      + intro nyLi.
        destruct y.
        apply opp_le'_x.
        apply H.
      + intro nxRi.
        clear opp_le'_x.
        destruct x.
        apply opp_le'.
        apply H.
    - destruct 1 as [[yLi LExyL] | [xRi LExRy]].
      + right.
        destruct y.
        exists yLi.
        apply opp_le'_x.
        assumption.
      + left.
        clear opp_le'_x.
        destruct x.
        exists xRi.
        apply opp_le'.
        assumption.
  Qed.

  Theorem opp_le (x y : Game) : x <= y <-> -y <= -x.
  Proof.
    split.
    - apply opp_le'.
    - intro.
      eapply le_trans, le_trans.
      + apply opp_opp.
      + apply opp_le'.
        eassumption.
      + apply opp_opp.
  Qed.

  Add Morphism opp with signature (le --> le) as opp_le_compat.
  Proof.
    intros.
    apply -> opp_le.
    assumption.
  Qed.

  Theorem opp_nle (x y : Game) : y !<= x <-> -x !<= -y.
  Proof.
    split.
    - apply opp_le'.
    - intro.
      eapply le_nle_trans, nle_le_trans.
      + apply opp_opp.
      + apply opp_le'.
        eassumption.
      + apply opp_opp.
  Qed.

  Add Morphism opp with signature (nle --> nle) as opp_nle_compat.
  Proof.
    intros.
    apply -> opp_nle.
    assumption.
  Qed.

  Theorem opp_eq (x y : Game) : x == y <-> -x == -y.
  Proof.
    split.
    - destruct 1; split; apply -> opp_le; assumption.
    - destruct 1; split; apply <- opp_le; assumption.
  Qed.

  Add Morphism opp with signature (eq ==> eq) as opp_compat.
  Proof.
    intros.
    apply -> opp_eq.
    assumption.
  Qed.

  Definition zero : Game :=
    {|
      lefts := Empty_set_rect (fun _ => Game);
      rights := Empty_set_rect (fun _ => Game)
    |}.

  Notation "0" := zero : Game_scope.

  Theorem opp_0 : -0 == 0.
  Proof.
    split; split; intros [].
  Qed.

  Fixpoint add (x : Game) :=
    fix add_x (y : Game) : Game :=
      {|
        lefts i :=
          match i with
          | inl i' => lefts x i' + y
          | inr i' => add_x (lefts y i')
          end;
        rights i :=
          match i with
          | inl i' => rights x i' + y
          | inr i' => add_x (rights y i')
          end
      |}
  where "x + y" := (add x y) : Game_scope.

  Theorem add_step (x y : Game) :
    x + y = {|
      lefts i :=
        match i with
        | inl i' => lefts x i' + y
        | inr i' => x + lefts y i'
        end;
      rights i :=
        match i with
        | inl i' => rights x i' + y
        | inr i' => x + rights y i'
        end
    |}.
  Proof.
    destruct x, y.
    reflexivity.
  Qed.

  Lemma add_le' :
    forall (x y z w : Game),
      (x <= y -> z <= w -> x + z <= y + w) /\
      (y !<= x -> z <= w -> y + w !<= x + z) /\
      (x <= y -> w !<= z -> y + w !<= x + z).
  Proof.
    fix add_le' 1.
    intro x.
    fix add_le'_x 1.
    intro y.
    fix add_le'_x_y 1.
    intro z.
    fix add_le'_x_y_z 1.
    intro w.
    split; [| split].
    - intros LExy LEzw.
      apply le_step.
      split.
      + rewrite (add_step x z).
        intros [xLi | zLi].
        * destruct add_le' with (lefts x xLi) y z w as (_ & IH & _).
          apply IH.
          -- apply le_step.
             assumption.
          -- assumption.
        * destruct add_le'_x_y with (lefts z zLi) w as (_ & _ & IH).
          apply IH.
          -- assumption.
          -- apply le_step.
             assumption.
      + rewrite (add_step y w).
        intros [yRi | wRi].
        * destruct add_le'_x with (rights y yRi) z w as (_ & IH & _).
          apply IH.
          -- apply le_step.
             assumption.
          -- assumption.
        * destruct add_le'_x_y_z with (rights w wRi) as (_ & _ & IH).
          apply IH.
          -- assumption.
          -- apply le_step.
             assumption.
    - intros [[yLi LExyL] | [xRi LExRy]] LEzw.
      + left.
        rewrite add_step.
        exists (inl yLi).
        destruct add_le'_x with (lefts y yLi) z w as (IH & _ & _); auto.
      + right.
        rewrite add_step.
        exists (inl xRi).
        destruct add_le' with (rights x xRi) y z w as (IH & _ & _); auto.
    - intros LExy [[wLi LEzwL] | [zRi LEzRw]].
      + left.
        rewrite add_step.
        exists (inr wLi).
        destruct add_le'_x_y_z with (lefts w wLi) as (IH & _ & _); auto.
      + right.
        rewrite add_step.
        exists (inr zRi).
        destruct add_le'_x_y with (rights z zRi) w as (IH & _ & _); auto.
  Qed.

  Add Morphism add with signature (le ++> le ++> le) as add_le_compat.
  Proof.
    intros.
    apply add_le'; assumption.
  Qed.

  Add Morphism add with signature (nle ++> le --> nle) as add_nle_le_compat.
  Proof.
    intros.
    edestruct add_le' as (_ & ? & _).
    eauto.
  Qed.

  Add Morphism add with signature (le --> nle ++> nle) as add_le_nle_compat.
  Proof.
    intros.
    edestruct add_le' as (_ & _ & ?).
    eauto.
  Qed.

  Add Morphism add with signature (eq ==> eq ==> eq) as add_compat.
  Proof.
    intros x y [LExy LEyx] z w [LEzw LEwz].
    split.
    - rewrite LExy, LEzw.
      reflexivity.
    - rewrite LEyx, LEwz.
      reflexivity.
  Qed.

  Lemma opp_add_le (x y : Game) : -x + -y <= -(x + y).
  Proof.
    revert x y.
    fix opp_add 1.
    intro x.
    fix opp_add_x 1.
    intro y.
    repeat rewrite add_step.
    split.
    - intros [xRi | yRi]; left.
      + revert xRi.
        rewrite (opp_step x).
        intro xRi.
        exists (inl xRi).
        apply opp_add.
      + revert yRi.
        rewrite (opp_step y).
        intro yRi.
        exists (inr yRi).
        apply opp_add_x.
    - intros [xLi | yLi]; right.
      + revert xLi.
        rewrite (opp_step x).
        intro xLi.
        exists (inl xLi).
        apply opp_add.
      + revert yLi.
        rewrite (opp_step y).
        intro yLi.
        exists (inr yLi).
        apply opp_add_x.
  Qed.

  Lemma opp_add_le_r (x y : Game) : -(x + y) <= -x + -y.
  Proof.
    revert x y.
    fix opp_add 1.
    intro x.
    fix opp_add_x 1.
    intro y.
    repeat rewrite add_step.
    split.
    - intros [xRi | yRi]; left.
      + revert xRi.
        rewrite (opp_step x).
        intro xRi.
        exists (inl xRi).
        apply opp_add.
      + revert yRi.
        rewrite (opp_step y).
        intro yRi.
        exists (inr yRi).
        apply opp_add_x.
    - intros [xLi | yLi]; right.
      + revert xLi.
        rewrite (opp_step x).
        intro xLi.
        exists (inl xLi).
        apply opp_add.
      + revert yLi.
        rewrite (opp_step y).
        intro yLi.
        exists (inr yLi).
        apply opp_add_x.
  Qed.

  Theorem opp_add (x y : Game) : -x + -y == -(x + y).
  Proof.
    split.
    - apply opp_add_le.
    - apply opp_add_le_r.
  Qed.

  Lemma add_comm_le (x y : Game) : x + y <= y + x.
  Proof.
    revert x y.
    fix add_comm_le 1.
    intro x.
    fix add_comm_le_x 1.
    intro y.
    repeat rewrite add_step.
    split.
    - intro xyLi.
      left.
      destruct xyLi as [xLi | yLi].
      + exists (inr xLi).
        apply add_comm_le.
      + exists (inl yLi).
        apply add_comm_le_x.
    - intro yxRi.
      right.
      destruct yxRi as [yRi | xRi].
      + eexists (inr yRi).
        apply add_comm_le_x.
      + eexists (inl xRi).
        apply add_comm_le.
  Qed.

  Theorem add_comm (x y : Game) : x + y == y + x.
  Proof.
    split; apply add_comm_le.
  Qed.

  Lemma add_assoc_le (x y z : Game) : x + (y + z) <= (x + y) + z.
  Proof.
    revert x y z.
    fix add_assoc_le 1.
    intro x.
    fix add_assoc_le_x 1.
    intro y.
    fix add_assoc_le_x_y 1.
    intro z.
    rewrite le_step.
    simpl.
    split.
    - intro x_yzLi.
      left.
      revert x_yzLi.
      rewrite (add_step x (y + z)).
      intros [xLi |].
      + rewrite (add_step (x + y) z), (add_step x y).
        exists (inl (inl xLi)).
        simpl.
        apply add_assoc_le.
      + rewrite (add_step y z).
        intros [yLi | zLi].
        * rewrite (add_step (x + y) z), (add_step x y).
          exists (inl (inr yLi)).
          apply add_assoc_le_x.
        * rewrite (add_step (x + y) z).
          exists (inr zLi).
          apply add_assoc_le_x_y.
    - intro xy_zRi.
      right.
      revert xy_zRi.
      rewrite (add_step (x + y) z).
      intros [| zRi].
      + rewrite (add_step x y).
        intros [xRi | yRi].
        * rewrite (add_step x (y + z)).
          exists (inl xRi).
          apply add_assoc_le.
        * rewrite (add_step x (y + z)), (add_step y z).
          exists (inr (inl yRi)).
          apply add_assoc_le_x.
      + rewrite (add_step x (y + z)), (add_step y z).
        exists (inr (inr zRi)).
        apply add_assoc_le_x_y.
  Qed.

  Lemma add_assoc_le_r (x y z : Game) : (x + y) + z <= x + (y + z).
  Proof.
    apply opp_le.
    repeat rewrite opp_add_le_r.
    repeat rewrite <- opp_add_le.
    apply add_assoc_le.
  Qed.

  Theorem add_assoc (x y z : Game) : x + (y + z) == (x + y) + z.
  Proof.
    split.
    - apply add_assoc_le.
    - apply add_assoc_le_r.
  Qed.

  Theorem add_0_l (x : Game) : 0 + x == x.
  Proof.
    induction x as [XLeft xLefts IHxLefts XRight xRights IHxRights].
    split.
    - split.
      + intros [[] | xLi].
        left.
        exists xLi.
        apply IHxLefts.
      + intros xRi.
        right.
        exists (inr xRi).
        apply IHxRights.
    - split.
      + intros xLi.
        left.
        exists (inr xLi).
        apply IHxLefts.
      + intros [[] | xLi].
        right.
        exists xLi.
        apply IHxRights.
  Qed.

  Theorem add_0_r (x : Game) : x + 0 == x.
  Proof.
    eapply eq_trans.
    - apply add_comm.
    - apply add_0_l.
  Qed.

  Theorem opp_def (x : Game) : x + -x == 0.
  Proof.
    induction x as [XLeft xLefts IHxLefts XRight xRights IHxRights].
    split.
    - split.
      + intros [xLi | xRi]; right; simpl.
        * rewrite add_step.
          exists (inr xLi).
          apply IHxLefts.
        * rewrite (add_step {| lefts := xLefts; rights := xRights |}).
          exists (inl xRi).
          apply IHxRights.
      + intros [].
    - split.
      + intros [].
      + intros [xRi | xLi]; left; simpl.
        * rewrite add_step.
          exists (inr xRi).
          apply IHxRights.
        * rewrite (add_step {| lefts := xLefts; rights := xRights |}).
          exists (inl xLi).
          apply IHxLefts.
  Qed.

  Definition sub (x y : Game) : Game := x + -y.

  Infix "-" := sub : Game_scope.

  Theorem sub_def (x y : Game) : x - y == x + -y.
  Proof.
    reflexivity.
  Qed.

  Add Morphism sub with signature (le ++> le --> le) as sub_le_compat.
  Proof.
    intros x y LExy z w LEwz.
    unfold sub.
    rewrite LExy, LEwz.
    reflexivity.
  Qed.

  Add Morphism sub with signature (nle ++> le ++> nle) as sub_nle_le_compat.
  Proof.
    intros.
    apply add_nle_le_compat.
    - assumption.
    - apply -> opp_le.
      assumption.
  Qed.

  Add Morphism sub with signature (le --> nle --> nle) as sub_le_nle_compat.
  Proof.
    intros.
    apply add_le_nle_compat.
    - assumption.
    - apply -> opp_nle.
      assumption.
  Qed.

  Add Morphism sub with signature (eq ==> eq ==> eq) as sub_compat.
  Proof.
    intros x y Exy z w Ezw.
    unfold sub.
    rewrite Exy, Ezw.
    reflexivity.
  Qed.

End Game.

Bind Scope Game_scope with Game Game.t.

Infix "<=" := Game.le : Game_scope.
Infix "!<=" := Game.nle (at level 70, no associativity) : Game_scope.
Infix "==" := Game.eq (at level 70, no associativity) : Game_scope.
Infix "<" := Game.lt.
Notation "- x" := (Game.opp x) : Game_scope.
Notation "0" := Game.zero : Game_scope.
Infix "+" := Game.add : Game_scope.
Infix "-" := Game.sub : Game_scope.
