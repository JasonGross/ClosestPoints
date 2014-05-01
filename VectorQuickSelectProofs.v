Require Export VectorQuickSelect.

Lemma vector_transport_minus_elim A k' x n'' H v
      (P : forall n, Vector.t A n -> Prop)
      (H0 : P _ (x::v)%vector)
: P _ (@vector_transport_minus A k' x n'' H v).
Proof.
  generalize dependent n''.
  induction k'; simpl in *;
  intros;
  repeat match goal with
           | [ |- appcontext[match ?n with _ => _ end] ] => destruct n
           | [ |- appcontext[S (S ?x) - S ?y] ] => change (S (S x) - S y) with (S x - y)
         end;
  eauto.
Defined.

Lemma vector_transport_eq_eq A n v H
: @vector_transport_eq A n n H v = v.
Proof.
  induction v; simpl; f_equal; trivial.
Qed.

Lemma vector_transport_eq_elim A n m v H
      (P : forall n, Vector.t A n -> Prop)
      (H0 : P _ v)
: P _ (@vector_transport_eq A n m H v).
Proof.
  subst.
  rewrite vector_transport_eq_eq.
  trivial.
Defined.


Inductive vector_split_correct_order A : forall x y z, Vector.t A x -> Vector.t A y -> Vector.t A z -> Type :=
| split_nil : vector_split_correct_order (Vector.nil _) (Vector.nil _) (Vector.nil _)
| split_left : forall x y z v1 v2 v3,
                 @vector_split_correct_order A x y z v1 v2 v3
                 -> forall k,
                      vector_split_correct_order (Vector.cons _ k _ v1) v2 (Vector.cons _ k _ v3)
| split_right : forall x y z v1 v2 v3,
                  @vector_split_correct_order A x y z v1 v2 v3
                  -> forall k,
                       vector_split_correct_order v1 (Vector.cons _ k _ v2) (Vector.cons _ k _ v3).

Notation "[]" := (Vector.nil _) : vector_scope.
Notation "h :: t" := (Vector.cons _ h _ t) (at level 60, right associativity) : vector_scope.
Bind Scope vector_scope with Vector.t.
Delimit Scope vector_scope with vector.

Eval lazy in (fun n => @vector_quick_select nat le le_dec (div2 (S n)) (S n) (lt_div2 _ (lt_0_Sn _))) _ (1::5::2::15::13::[])%vector.

Definition test_qselect := Eval lazy in (fun n => @vector_quick_select nat le le_dec (div2 (S n)) (S n) (lt_div2 _ (lt_0_Sn _))) _ (1::2::3::4::5::[])%vector.
Check eq_refl : test_qselect = (inleft 3, 1::2::[], 3::4::5::[])%vector.



Hint Constructors vector_split_correct_order Vector.Forall and.

Section median.
  Local Hint Extern 0 => progress subst_body.

  Ltac revert_body_then tac :=
    match goal with
      | [ H := _ |- _ ] => revert H;
                          revert_body_then tac;
                          intro
      | _ => tac
    end.

  Ltac subst_lt_1 :=
    match goal with
      | [ H : _ < 1 |- _ ] => let H' := fresh in
                              pose proof (proj1 (Nat.lt_1_r _) H) as H'
    end;
    revert_body_then ltac:(subst).

  Hint Extern 0 => subst_lt_1.

  Hint Extern 1 => progress simpl in *.

  Add Parametric Morphism A n v : (fun P => @Vector.Forall A P n v)
      with signature (pointwise_relation _ impl) ==> impl
        as Vector_Forall_impl.
  Proof.
    induction v; lazy in *; eauto.
    intros x y H H'.
    inversion H'; simpl_existT; subst; constructor; eauto.
  Qed.


  Local Ltac t' :=
    match goal with
      | _ => solve [ eauto ]
      | _ => solve [ exfalso; eauto ]
      | _ => progress simpl in *
      | _ => subst_lt_1
      | [ |- appcontext[match ?E with end] ] => case E
      | _ => intro
      | _ => progress destruct_head and
      | _ => progress destruct_head sum
      | _ => progress destruct_head sumbool
      | _ => progress subst
      | _ => split
      | [ v : Vector.t _ 0 |- _ ]
        => generalize dependent v;
          refine (@Vector.case0 _ _ _)
      | [ |- appcontext[if ?E then _ else _] ] => destruct E
      | _ => progress subst_body
      | [ H : _ |- _ ] => apply total_decidable_neg_flip in H
      | [ H : 0 < S _ |- _ ] => clear H
      | _ => eapply Vector.Forall_cons; solve [ repeat t' ]
      | _ => eapply Vector_Forall_impl; try eassumption; [ ]; lazy; solve [ repeat t' ]
      | _ => solve [ etransitivity; eauto ]
      | [ |- appcontext[match lt_eq_lt_dec ?n ?k with _ => _ end] ]
        => destruct (lt_eq_lt_dec n k)
      | [ |- appcontext[@vector_transport_minus ?A ?k' ?x ?n'' ?H ?v] ]
        => refine (@vector_transport_minus_elim A k' x n'' H v _ _)
      | _ => apply vector_transport_eq_elim
      | [ IH : _, fH : _ |- appcontext[match fst (fst (?f ?y ?H' ?k ?H'' ?v)) with _ => _ end] ]
        => pose proof (IH y H' k H'' v);
          pose proof (fH y H' k H'' v);
          generalize dependent (f y H' k H'' v);
          intros [ [ [?|?] ?] ? ]
      | [ IH : _, fH : _ |- appcontext[snd (fst (?f ?y ?H' ?k ?H'' ?v))] ]
        => pose proof (IH y H' k H'' v);
          pose proof (fH y H' k H'' v);
          generalize dependent (f y H' k H'' v);
          intros [ [ [?|?] ?] ? ]
    end.
  Local Ltac t := repeat t'.

  Lemma vector_quick_select_helper_correct_median
        A (le : A -> A -> Prop)
        (le_dec : forall x y, {le x y} + {~le x y})
        `{Hr : PreOrder _ le}
        `{Ht : Total _ le}
        `{Hd : forall x y, Decidable (le x y)}
        (x : nat)
        (f : ∀ y : nat,
               y < x
               → ∀ k : nat, k < y → t A y → (A + {y = 0}) * t A k * t A (y - k))
        (fH : forall y H' k H'' v P,
                Vector.Forall P v
                <-> Vector.Forall P (snd (fst (f y H' k H'' v)))
                    /\ Vector.Forall P (snd (f y H' k H'' v)))
        (IH : forall y H' k H'' v
                     (res := f y H' k H'' v)
                     (lefts := snd (fst res))
                     (rights := snd res),
                match fst (fst res) with
                  | inleft median =>
                    Vector.Forall (λ x0 : A, le x0 median) lefts
                    ∧ Vector.Forall (λ x0 : A, le median x0) rights
                  | inright _ => y = 0
                end)
        (v : t A x) (k : nat) (H : k < x)
        (res := vector_quick_select_helper le le_dec f H v)
        (lefts := snd (fst res))
        (rights := snd res)
  : match fst (fst res) with
      | inleft median =>
        Vector.Forall (λ x0 : A, le x0 median) lefts
        ∧ Vector.Forall (λ x0 : A, le median x0) rights
      | inright _ => x = 0
    end.
  Proof.
    destruct v; t; [ ].
    { destruct v; t; [ ].
      destruct k; t;
      try solve [ destruct k; t ].
      admit.
      admit. }
  Qed.

(*Lemma vector_split_correct_median
      A (le : A -> A -> Prop)
      (le_dec : forall x y, {le x y} + {~le x y})
      k n
      (H : k < n)
      (v : Vector.t A n)
      (res := @vector_quick_select A le le_dec k _ H v)
      (lefts := snd (fst res))
      (rights := snd res)
: match fst (fst res) with
    | inleft median
      => Vector.Forall (fun x => le x median) lefts
         /\ Vector.Forall (fun x => le median x) rights
    | inright _ => n = 0
  end.
Proof.
  revert v k H res lefts rights.
  apply (Fix lt_wf) with (x := n); clear n.
  induction n.
  { intros v k H.
    inversion H. }
  { unfold vector_quick_select.

    let n := match type of v with | t ?A ?n => constr:(n) end in
    set (n' := n) in v;
      change n with n';
      assert (n' = n) by reflexivity
      generalize dependent n'.

  unfold vector_quick_select in res.
  subst_body.
  erewrite Fix_eq.*)
End median.

Lemma vector_split_correct_order_refl1 A x v
: @vector_split_correct_order A _ x _ (Vector.nil _) v v.
Proof.
  induction v; eauto.
Qed.

Lemma vector_split_correct_order_refl2 A x v
: @vector_split_correct_order A x _ _ v (Vector.nil _) v.
Proof.
  induction v; eauto.
Qed.

Hint Resolve vector_split_correct_order_refl1 vector_split_correct_order_refl2.

Lemma quick_select_correct A (le : A -> A -> Prop)
      (le_dec : forall x y, {le x y} + {~le x y})
      k n
      (H : k < n)
      (v : Vector.t A n)
      (res := @vector_quick_select A le le_dec k n H v)
: vector_split_correct_order (snd (fst res)) (snd res) v.
Proof.
  unfold vector_quick_select in res.
  subst res.
  revert k H.
  induction v; eauto.
  { simpl.
    induction k; intros; simpl in *.
    { erewrite Coq.Init.Wf.Fix_eq; destruct v; simpl in *; eauto;
      admit. (*repeat (intro || apply functional_extensionality_dep);
      unfold vector_quick_select_helper;
      destruct_in_match_if atomic; rewrite_hyp; simpl; trivial.
      destruct_in_match_if ltac:(fun _ => idtac);
      simpl; subst; trivial. *) }
    { erewrite Coq.Init.Wf.Fix_eq; destruct v; simpl in *; eauto;
      try do 2 destruct_in_match_if' ltac:(fun _ => idtac);
      simpl;
      eauto;
      admit. }
  }
Qed.
