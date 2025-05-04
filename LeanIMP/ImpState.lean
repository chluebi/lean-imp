import LeanIMP.Basic
open Classical


def IMPState.ext_eq (s1 s2 : IMPState) : Prop :=
  forall (k : String), IMPState.lookup s1 k = IMPState.lookup s2 k

theorem IMPState.lookup_congr (k : String) {s1 s2 : IMPState} (h : IMPState.ext_eq s1 s2) :
  IMPState.lookup s1 k = IMPState.lookup s2 k :=
  h k

theorem IMPState.ext_eq_reflexive (s : IMPState) : IMPState.ext_eq s s :=
  by
    unfold IMPState.ext_eq
    intros k
    eq_refl

theorem IMPState.ext_eq_symmetric {s1 s2 : IMPState} : (IMPState.ext_eq s1 s2) -> (IMPState.ext_eq s2 s1)  :=
  by
    unfold IMPState.ext_eq
    intros ass k
    symm
    apply ass


theorem IMPState.ext_eq_transitive {s1 s2 s3 : IMPState} : (IMPState.ext_eq s1 s2) -> (IMPState.ext_eq s2 s3) -> (IMPState.ext_eq s1 s3)  :=
  by
    intros ass1 ass2
    unfold IMPState.ext_eq
    intros k
    rw [ass1]
    apply ass2


instance : Equivalence IMPState.ext_eq where
  refl := IMPState.ext_eq_reflexive
  symm := IMPState.ext_eq_symmetric
  trans := IMPState.ext_eq_transitive


theorem IMPState.update_twice_eq_update_once (s : IMPState) (k_update : String) (v1 v2 : Int) :
  IMPState.ext_eq (IMPState.update (s.update k_update v1) k_update v2) (s.update k_update v2) :=
    by
      unfold ext_eq
      intros k
      have h_lem : (k = k_update) ∨ ¬(k = k_update) := by apply em
      cases h_lem with
        | inl h_eq =>
          unfold lookup
          simp
          unfold update
          unfold List.find?
          simp
          cases h_eq_bool : (k_update == k) with
            | true => simp
            | false =>
              rw [h_eq] at h_eq_bool
              conv at h_eq_bool =>
                lhs
                rw [beq_self_eq_true]
              contradiction -- contradiction, we are in the case where they are equal
        | inr h_neq =>
          unfold lookup
          simp
          unfold update
          unfold List.find?
          simp
          cases h_eq_bool : (k_update == k) with
            | true => simp -- contradiction, we are in the case where they are not equal
            | false =>
              simp
              conv =>
                lhs
                unfold List.find?
              simp
              cases h_eq_bool2 : (k_update == k) with
              | true =>
                rw [h_eq_bool2] at h_eq_bool
                contradiction -- contradiction, we are in the case where they are not equal
              | false =>
                simp


theorem IMPState.update_unrelated_eq_update_once (s : IMPState) (k1 k2: String) (v1 v2 : Int) (k1_neq_k2 : ¬(k1 = k2)) :
  (IMPState.update (s.update k1 v1) k2 v2).lookup k1 = (s.update k1 v1).lookup k1 :=
  by
    unfold update
    unfold List.lookup
    simp
    cases h_eq_bool : (k1 == k2) with
      | true =>
        have eq : k1 = k2 := by
          apply decide_eq_true_iff.mp
          exact h_eq_bool -- contradiction, we have an assumption that contradicts that
        contradiction
      | false =>
        simp
