Require Export Vector NPeano Div2 NArith Wf Wf_nat Program Omega.
Require Export Program.Equality.
Require Export CommonDefinitions ClosestPoints.Tactics.

Fixpoint count_occ_acc A B (P : B -> A -> B * bool) (acc : B) n (v : Vector.t A n)
: nat
  := match v with
       | Vector.nil => 0
       | Vector.cons x _ xs => let Px := P acc x in
                               (if snd Px then 1 else 0) + count_occ_acc P (fst Px) xs
     end.

Fixpoint vector_partition A B (f : B -> A -> B * bool) (acc : B) n (v : Vector.t A n)
: Vector.t A (count_occ_acc f acc v) * Vector.t A (n - count_occ_acc f acc v).
Proof.
  refine match v as v in Vector.t _ n return
               Vector.t A (count_occ_acc f acc v) * Vector.t A (n - count_occ_acc f acc v)
         with
           | Vector.nil => (Vector.nil _, Vector.nil _)
           | Vector.cons x n' xs => let fax := f acc x in
                                    let xs_part := (@vector_partition _ _ f (fst fax) _ xs) in
                                    if snd fax as fx return
                                       (Vector.t A ((if fx then 1 else 0) + count_occ_acc f (fst fax) xs) *
                                        Vector.t A (S n' - ((if fx then 1 else 0) + count_occ_acc f (fst fax) xs)))
                                    then (Vector.cons _ x _ (fst xs_part),
                                          snd xs_part)
                                    else (fst xs_part,
                                          _)
         end.
  generalize (snd xs_part); clear xs_part n v.
  change (0 + ?n) with n.
  generalize (count_occ_acc f (fst fax) xs); clear fax.
  intro n.
  clear xs.
  revert n'.
  induction n; intro n'.
  - exact (fun v' =>
             Vector.cons
               _ x _
               (match n' as n' return Vector.t A (n' - 0) -> Vector.t A n' with
                  | 0 => fun v' => v'
                  | S n'' => fun v' => v'
                end v')).
  - destruct n'.
    + exact (fun v' => v').
    + exact (IHn _).
Defined.

Definition acc_at_most (at_most : nat) A (f : A -> bool) : nat -> A -> nat * bool
  := fun count a => if lt_dec count at_most
                    then ((if f a then 1 else 0) + count, f a)
                    else (count, false).

Definition vector_partition_at_most A (f : A -> bool) (at_most : nat) n (v : Vector.t A n)
  := vector_partition (acc_at_most at_most f)
                      0
                      v.

Fixpoint vector_transport_eq
         {A n} {m} {H : n = m} (v : Vector.t A n)
: Vector.t A m.
Proof.
  revert H.
  refine match v in (Vector.t _ n), m as m return n = m -> Vector.t A m with
           | Vector.nil, 0 => fun _ => Vector.nil _
           | Vector.cons x _ xs, S m' => fun H => Vector.cons _ x _ (@vector_transport_eq A _ m' (f_equal pred H) xs)
           | Vector.nil, S _ => fun H => !
           | Vector.cons _ _ _, 0 => fun H => !
         end;
  revert H; clear; abstract eauto.
Defined.

Fixpoint vector_transport_minus
         (A : Type) (k' : nat) (x : A) {struct k'}
: ∀ n'' : nat,
    S k' < n'' → Vector.t A (n'' - S k') → Vector.t A (n'' - k').
Proof.
  destruct k'.
  - clear vector_transport_minus.
    intros n'' H v.
    destruct n'' as [|[|n'']].
    + exfalso; eauto.
    + exact (Vector.cons _ x _ v).
    + exact (Vector.cons _ x _ v).
  - intros n'' H v.
    destruct n'' as [|[|n'']].
    + exfalso; eauto.
    + exfalso; apply lt_S_n in H; eauto.
    + exact (@vector_transport_minus A _ x _ (lt_S_n _ _ H) v).
Defined.

Arguments vector_transport_minus _ !_ _ _ _ _.

Hint Extern 0 => match goal with H : ?x < ?x |- _ => destruct (@lt_irrefl _ H) end.

Definition tag {T T'} (tag : T') (x : T) := x.

Arguments tag / .

Definition vector_quick_select_helper
: ∀ (A : Type) (le : A → A → Prop),
    (∀ x y : A, {le x y} + {¬le x y})
    → ∀ x : nat,
        (∀ y : nat,
           y < x
           → ∀ k : nat,
               k < y
               → Vector.t A y → (A + {y = 0}) * Vector.t A k * Vector.t A (y - k))
        → ∀ k : nat,
            k < x
            → Vector.t A x → (A + {x = 0}) * Vector.t A k * Vector.t A (x - k).
Proof.
  intros A le le_dec.
  intros n vector_quick_select k H v.
  refine (match v as v' in Vector.t _ n', k as k' return
                n' = n -> k' < n' -> (A + {n' = 0}) * Vector.t A k' * Vector.t A (n' - k')
          with
            | Vector.nil, 0 => fun _ _ => (inright eq_refl, Vector.nil _, Vector.nil _)
            | Vector.nil, S k' => fun _ H => match lt_n_0 _ H : False with end
            | Vector.cons x n'' xs, 0 =>
              match xs as xs' in Vector.t _ n''' return
                    S n''' = n -> 0 < S n''' -> _
              with
                | Vector.nil => fun _ _ => (inleft x, Vector.nil _, Vector.cons _ x _ (Vector.nil _))
                | Vector.cons y n''' ys =>
                  fun _ _ =>
                    let rest := @vector_quick_select _ _ 0 (lt_0_Sn _) (Vector.cons _ y _ ys) in
                    let min_v := fst (fst rest) in
                    (match min_v with
                       | inright pf0 => inleft (tag 0 x)
                       | inleft min_v' => inleft (tag 1 (if le_dec x min_v' then x else min_v'))
                     end,
                     match snd (fst rest) in Vector.t _ n return n = 0 -> Vector.t _ n with
                       | Vector.nil => fun _ => Vector.nil _
                       | Vector.cons _ _ _ => fun H => match Nat.neq_succ_0 _ H : False with end
                     end eq_refl,
                     Vector.cons _ (tag 2 x) _ (snd rest))
              end
            | Vector.cons x n'' xs, S k' =>
              fun H' H =>
                let rest_k' := @vector_quick_select _ _ k' (le_S_n _ _ H) xs in
                match (fst (fst rest_k')) with
                  | inright pf1 => match lt_n_0 _ (lt_S_n _ _ (@eq_rect nat _ (fun n'' => _ < S n'') H _ pf1)) with end
                  | inleft fst_rest_k' =>
                    if le_dec x fst_rest_k'
                    (** If we are smaller than the [k']th element, then we belong on the left, and can reuse the same value for the [S k']th element *)
                    then (inleft (tag 3 fst_rest_k'),
                          Vector.cons _ (tag 4 x) _ (snd (fst rest_k')),
                          snd rest_k')
                    else match lt_eq_lt_dec n'' (S k') with
                           | inleft (left n''_lt_Sk') =>
                             match le_Sn_n _ (le_trans _ _ _ H n''_lt_Sk') with end
                           | inleft (right n''_eq_Sk') => (** We are larger than the [k']th element, and, in fact, the only such element (because [S k' = n'']), so we have the element we are looking for *)
                             (** XXX We want to say that [xs = snd (fst rest_k') ++ snd rest_k'] up to permutation *)
                             (inleft (tag 5 x),
                              vector_transport_eq xs,
                              vector_transport_eq (tag 6 x::[])%vector)
                           | inright Sk'_lt_n'' => (** We are larger than the [k']th element, so we go on the right of the [S k'] partition *)
                             let rest_Sk' := @vector_quick_select _ _ (S k') Sk'_lt_n'' xs in
                             (inleft (match (fst (fst rest_Sk')) with
                                        | inright pf1 => !
                                        | inleft fst_rest_Sk'
                                          => tag 7 (if le_dec fst_rest_Sk' x then fst_rest_Sk' else x)
                                      end),
                              tag 9 (snd (fst rest_Sk')),
                              vector_transport_minus (tag 8 x) (Sk'_lt_n'') (snd rest_Sk'))
                         end
                end
          end eq_refl H);
    clear vector_quick_select;
    try solve [
          repeat match goal with
                   | [ H : _ = ?n |- appcontext[?n] ] => revert H
                   | [ H : ?n = 0, H' : S _ < ?n |- _ ]
                     => exfalso; revert H H'
                 end;
          clear; intros;
          abstract (subst; eauto; omega)
        ].
Defined.

(** We get the [k]th largest element (0 means smallest), and partition the array into elements [<=] the [k]th one, andx [>=] the [k]th one.  The [k]th element sits in the second vector.  If [k > n], then the first list contains everything, and the second list is [nil]. *)
Definition vector_quick_select A (le : A -> A -> Prop)
         (le_dec : forall x y, {le x y} + {~le x y})
         k n
         (H : k < n)
         (v : Vector.t A n)
: (A + {n = 0}) * Vector.t A k * Vector.t A (n - k).
Proof.
  revert k H v.
  apply (Fix lt_wf) with (x := n); clear n.
  exact (@vector_quick_select_helper A le le_dec).
Defined.
