import LeanIMP.Basic
import LeanIMP.SmallStepBasic

theorem small_step_sequence_composeable {α: Type} [BEq α] {p1 p2: IMPProgram α} {s s' s'' : IMPState α} {k1 k2: Nat} :
 SmallStepSequence p1 s s' k1 ->
 SmallStepSequence p2 s' s'' k2 ->
 SmallStepSequence (IMPProgram.seq p1 p2) s s'' (k1 + k2) :=
 by
  intros step1 step2
  induction step1 with
    | single p s s' tree1 =>
      have tree1_step := SmallStep.ss_seq1 p p2 s s' tree1
      exact SmallStepSequence.cons (IMPProgram.seq p p2) p2 s s' s'' k2 tree1_step step2
    | cons p1 p2_cons s s' s''_cons k next tail ih =>
      have ih := ih step2
      have next_step := SmallStep.ss_seq2 p1 p2 p2_cons s s' next
      rw [Nat.add_assoc]
      exact SmallStepSequence.cons (IMPProgram.seq p1 p2) (IMPProgram.seq p2_cons p2) s s' s'' (k+k2) next_step ih


theorem small_step_sequence_gt_zero {α: Type} [BEq α] {p: IMPProgram α} {s s': IMPState α} {k: Nat}
  (seq: SmallStepSequence p s s' k) : k > 0 := by
    induction seq with
      | single _ _ _ => trivial
      | cons _ _ _ _ _ k _ _ ih => exact Nat.add_pos_right 1 ih


-- https://github.com/leanprover/lean4/blob/ff6eb56f5c0ffff7b0c6b27add542e725767f37b/tests/playground/pge.lean
theorem lt_or_eq_of_succ {i j:Nat} (lt : i < Nat.succ j) : i < j ∨ i = j :=
  match lt with
  | Nat.le.step m => Or.inl m
  | Nat.le.refl => Or.inr rfl

theorem strong_induction_on (p : Nat → Prop) (n:Nat)
  (h:∀n, (∀ m, m < n → p m) → p n) : p n := by
    suffices ∀n m, m < n → p m from this (Nat.succ n) n (Nat.lt_succ_self _)
    intros n
    induction n with
    | zero =>
      intros m h
      contradiction
    | succ i ind =>
      intros m h1
      cases lt_or_eq_of_succ h1 with
      | inl is_lt =>
        apply ind _ is_lt
      | inr is_eq =>
        apply h
        rw [is_eq]
        apply ind


theorem small_step_sequence_seperable {α: Type} [BEq α] :
  ∀k: Nat, ∀p1 p2: IMPProgram α, ∀s s'': IMPState α, SmallStepSequence (IMPProgram.seq p1 p2) s s'' k ->
  ∃k1 k2: Nat, ∃s': IMPState α, And (And (SmallStepSequence p1 s s' k1) (SmallStepSequence p2 s' s'' k2)) (k1 + k2 = k) :=
    by
      intros k
      refine strong_induction_on (fun x => (∀p1 p2: IMPProgram α, ∀s s'': IMPState α, (⟨p1.seq p2,s⟩ ->* [x] s'') -> ∃k1' k2': Nat, ∃s': IMPState α, And (And (SmallStepSequence p1 s s' k1') (SmallStepSequence p2 s' s'' k2')) (k1' + k2' = x))) k ?_
      simp
      intros n
      intros ih
      intros p1 p2
      intros s s''
      intros composed_sequence
      cases composed_sequence with
        | single tree =>
          exists 1
        | cons p1 p2_cons s s' s'' k1 step rest =>
          cases step with
            | ss_seq1 p1 p2 _ _ ih_finished =>
              exists 1
              exists k1
              constructor
              exists s'
              exact And.intro (SmallStepSequence.single p1 s s' ih_finished) rest
              simp
            | ss_seq2 p1 p2 p3 s s' ih_unfinished =>
              have k_less : k1 < 1 + k1 := by
                rw [Nat.add_comm]
                exact Nat.lt_add_one k1
              have ⟨k1_, k2_, ⟨inbetween, ⟨step1, step2⟩⟩, arith⟩ := ih k1 k_less p3 p2 s' s'' rest
              have a := SmallStepSequence.cons p1 p3 s s' inbetween k1_ ih_unfinished step1
              exists (k1_+1)
              exists k2_
              constructor
              exists inbetween
              constructor
              rw [Nat.add_comm]
              exact a
              exact step2
              conv =>
                arg 1
                arg 1
                rw [Nat.add_comm]
              rw [Nat.add_assoc]
              rw [arith]
