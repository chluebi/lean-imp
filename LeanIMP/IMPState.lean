import LeanIMP.Basic



def IMPState.ext_eq {α: Type} [BEq α] (s1 s2 : IMPState α) : Prop :=
  forall (k : α), s1.lookup k = s2.lookup k

theorem IMPState.lookup_congr {α: Type} [BEq α] (k : α) {s1 s2 : IMPState α} (h : IMPState.ext_eq s1 s2) :
  s1.lookup k = s2.lookup k :=
  h k

theorem IMPState.ext_eq_reflexive {α: Type} [BEq α] (s : IMPState α) : IMPState.ext_eq s s :=
  by
    unfold IMPState.ext_eq
    intros k
    eq_refl

theorem IMPState.ext_eq_symmetric {α: Type} [BEq α] {s1 s2 : IMPState α} : (IMPState.ext_eq s1 s2) -> (IMPState.ext_eq s2 s1)  :=
  by
    unfold IMPState.ext_eq
    intros ass k
    symm
    apply ass


theorem IMPState.ext_eq_transitive {α: Type} [BEq α] {s1 s2 s3 : IMPState α} : (IMPState.ext_eq s1 s2) -> (IMPState.ext_eq s2 s3) -> (IMPState.ext_eq s1 s3)  :=
  by
    intros ass1 ass2
    unfold IMPState.ext_eq
    intros k
    rw [ass1]
    apply ass2


instance {α: Type} [beq : BEq α] : Equivalence (@IMPState.ext_eq α beq) where
  refl := IMPState.ext_eq_reflexive
  symm := IMPState.ext_eq_symmetric
  trans := IMPState.ext_eq_transitive


theorem IMPState.update_twice_eq_update_once {α: Type} [BEq α] (s : IMPState α) (k_update : α) (v1 v2 : Nat) :
  IMPState.ext_eq (IMPState.update (s.update k_update v1) k_update v2) (s.update k_update v2) :=
    by
      unfold ext_eq
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


theorem IMPState.update_unrelated_eq_update_once {α: Type} [BEq α] (s : IMPState α) (k1 k2: α) (v2 : Nat) (k1_neq_k2 : ¬(k1 == k2)) :
  (IMPState.update s k2 v2).lookup k1 = s.lookup k1 :=
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



theorem IMPState.prepend_update_eq_reverse_append {α: Type} [BEq α] (s1 s2: IMPState α) :
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
      unfold IMPState.update
      unfold List.foldr
      simp
      match tail with
        | List.nil => simp
        | List.cons _ _ =>
          simp

theorem IMPState.prepend_update_eq_reverse_Happend {α: Type} [BEq α] (s1 s2: IMPState α) :
  s1.prepend_updates s2 = s2 ++ s1 :=
  by
    exact IMPState.prepend_update_eq_reverse_append s1 s2


theorem IMPState.update_unrelated_eq_update_list {α: Type} [BEq α] [PartialEquivBEq α] (s1 s2 : IMPState α) (k: α) (s2_does_not_contain : IMPState.does_not_contain s2 k) :
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
      rw [<- IMPState.prepend_update_eq_reverse_Happend]
      apply ih
      exact s2_does_not_contain.right


macro "simp_monad" : tactic =>
  `(tactic| simp [Bind.bind, Monad.toBind, StateT.pure, StateT.run, StateT.instMonad, StateT.bind, StateT.map, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run])

theorem IMPState.eval_int_is_pure {α: Type} [BEq α] (s: IMPState α) (expr : NatExpr α) :
  (evalNatExpr expr) s = (((evalNatExpr expr) s).fst, s) :=
  by
    induction expr generalizing s with
    | var key =>
      simp [evalNatExpr]
      simp_monad
      match List.lookup key s with
        | none => eq_refl
        | some _ => eq_refl
    | const c =>
      simp [evalNatExpr]
      simp_monad
    | add a b ih_a ih_b
    | sub a b ih_a ih_b
    | mul a b ih_a ih_b =>
      simp [evalNatExpr]
      simp_monad
      rw [ih_a s]
      conv =>
        arg 1
        dsimp
      simp_monad
      rw [ih_b s]
