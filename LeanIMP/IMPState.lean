import LeanIMP.Basic


namespace IMPState

  def ext_eq {α: Type} [BEq α] (s1 s2 : IMPState α) : Prop :=
    forall (k : α), s1.lookup k = s2.lookup k

  theorem lookup_congr {α: Type} [BEq α] (k : α) {s1 s2 : IMPState α} (h : ext_eq s1 s2) :
    s1.lookup k = s2.lookup k :=
    h k

  theorem ext_eq_reflexive {α: Type} [BEq α] (s : IMPState α) : ext_eq s s :=
    by
      unfold ext_eq
      intros k
      eq_refl

  theorem ext_eq_symmetric {α: Type} [BEq α] {s1 s2 : IMPState α} : (ext_eq s1 s2) -> (ext_eq s2 s1)  :=
    by
      unfold ext_eq
      intros ass k
      symm
      apply ass


  theorem ext_eq_transitive {α: Type} [BEq α] {s1 s2 s3 : IMPState α} : (ext_eq s1 s2) -> (ext_eq s2 s3) -> (ext_eq s1 s3)  :=
    by
      intros ass1 ass2
      unfold ext_eq
      intros k
      rw [ass1]
      apply ass2


  instance IMPStateEquivalence {α: Type} [beq : BEq α] : Equivalence (@ext_eq α beq) where
    refl := ext_eq_reflexive
    symm := ext_eq_symmetric
    trans := ext_eq_transitive


  instance IMPStateSetoid (α: Type) [BEq α] : Setoid (IMPState α) where
    r := ext_eq
    iseqv := IMPStateEquivalence

  def IMPStateQ (α: Type) [BEq α] := Quotient (IMPStateSetoid α)

  theorem update_twice_eq_update_once {α: Type} [BEq α] (s : IMPState α) (k_update : α) (v1 v2 : Nat) :
    Quotient.mk' (update (s.update k_update v1) k_update v2) = Quotient.mk' (s.update k_update v2) :=
      by
        have is_ext_eq : ext_eq (update (s.update k_update v1) k_update v2) (s.update k_update v2) := by
          intros k
          cases h_lem_bool: k == k_update with
            | true =>
              unfold List.lookup
              unfold update
              simp
              rw [h_lem_bool]
            | false =>
              unfold List.lookup
              unfold update
              simp
              rw [h_lem_bool]
              simp
              unfold List.lookup
              rw [h_lem_bool]
              simp
              match s with
                | List.nil => simp
                | List.cons head tail =>
                  simp
                  rw [List.lookup]

        exact Quotient.sound is_ext_eq


  theorem update_unrelated_eq_update_once {α: Type} [BEq α] (s : IMPState α) (k1 k2: α) (v2 : Nat) (k1_neq_k2 : ¬(k1 == k2)) :
    (update s k2 v2).lookup k1 = s.lookup k1 :=
    by
      unfold update
      unfold List.lookup
      cases h_eq_bool : (k1 == k2) with
        | true =>
          have eq : k1 == k2 := by
            exact h_eq_bool
          contradiction
        | false =>
          match s with
            | List.nil => simp
            | List.cons head tail =>
              simp
              conv =>
                lhs
                unfold List.lookup



  theorem prepend_update_eq_reverse_append {α: Type} [BEq α] (s1 s2: IMPState α) :
    s1.prepend_updates s2 = s2.append s1 :=
    by
      induction s2 generalizing s1 with
      | nil =>
        unfold prepend_updates
        simp
      | cons head tail ih =>
        -- step case
        unfold prepend_updates
        simp
        unfold update
        unfold List.foldr
        simp
        match tail with
          | List.nil => simp
          | List.cons _ _ =>
            simp

  theorem prepend_update_eq_reverse_Happend {α: Type} [BEq α] (s1 s2: IMPState α) :
    s1.prepend_updates s2 = s2 ++ s1 :=
    by
      exact prepend_update_eq_reverse_append s1 s2


  theorem update_unrelated_eq_update_list {α: Type} [BEq α] [PartialEquivBEq α] (s1 s2 : IMPState α) (k: α) (s2_does_not_contain : does_not_contain s2 k) :
    (s1.prepend_updates s2).lookup k = s1.lookup k :=
    by
      induction s2 generalizing s1 with
      | nil =>
        unfold prepend_updates
        simp
      | cons head tail ih =>
        unfold prepend_updates
        simp
        unfold update
        have head_is_not : ¬(head.fst == k) := by
          apply s2_does_not_contain.left
        have head_is_not_symm : (k == head.fst) = false := by
          conv =>
            arg 1
            rw [BEq.comm]
          exact Eq.symm ((fun {a b} ↦ Bool.not_not_eq.mp) fun a ↦ head_is_not (id (Eq.symm a)))
        conv =>
          lhs
          unfold List.lookup
        rw [head_is_not_symm]
        simp
        rw [<- prepend_update_eq_reverse_Happend]
        apply ih
        exact s2_does_not_contain.right

  theorem eval_int_is_pure {α: Type} [BEq α] (s: IMPState α) (expr : NatExpr α) :
    (evalNatExpr expr) s = (((evalNatExpr expr) s).fst, s) :=
    by
      induction expr generalizing s with
      | var key =>
        simp [evalNatExpr]
        match List.lookup key s with
          | none => eq_refl
          | some _ => eq_refl
      | const c =>
        simp [evalNatExpr]
      | add a b ih_a ih_b
      | sub a b ih_a ih_b
      | mul a b ih_a ih_b =>
        simp [evalNatExpr]
        rw [ih_a s]
        conv =>
          arg 1
          dsimp
        simp
        rw [ih_b s]


  theorem eval_bool_is_pure {α: Type} [BEq α] (s: IMPState α) (expr : BoolExpr α) :
    (evalBoolExpr expr) s = (((evalBoolExpr expr) s).fst, s) :=
    by
      induction expr generalizing s with
      | var key =>
        simp [evalBoolExpr]
        match List.lookup key s with
          | none => eq_refl
          | some val =>
            match h: val with
              | 0 =>
                rfl
              | Nat.succ n =>
                rfl
      | const c =>
        simp [evalBoolExpr]
      | eq a b
      | neq a b
      | lt a b
      | leq a b
      | gt a b
      | geq  =>
        simp [evalBoolExpr]
        rw [eval_int_is_pure]
        simp
        rw [eval_int_is_pure]
      | and a b ih_a ih_b =>
        simp [evalBoolExpr]
        rw [ih_a s]
        conv =>
          arg 1
          dsimp
        match (evalBoolExpr a s) with
          | (true, _) =>
            simp
            exact (ih_b s)
          | (false, _) =>
            simp
      | or a b ih_a ih_b =>
        simp [evalBoolExpr]
        rw [ih_a s]
        conv =>
          arg 1
          dsimp
        match (evalBoolExpr a s) with
          | (true, _) =>
            simp
          | (false, _) =>
            simp
            exact (ih_b s)
      | not a ih_a =>
        simp [evalBoolExpr]
        rw [ih_a s]

end IMPState
