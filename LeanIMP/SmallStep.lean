import LeanIMP.Basic
import LeanIMP.SmallStepBasic

theorem small_step_sequence_composeable {α: Type} [BEq α] {p1 p2: IMPProgram α} {s s' s'' : IMPState α} :
 SmallStepSequence p1 s s' ->
 SmallStepSequence p2 s' s'' ->
 SmallStepSequence (IMPProgram.seq p1 p2) s s'' :=
 by
  intros step1 step2
  induction step1 with
    | single p s s' tree1 =>
      have tree1_step := SmallStep.ss_seq1 p p2 s s' tree1
      exact SmallStepSequence.cons (IMPProgram.seq p p2) p2 s s' s'' tree1_step step2
    | cons p1 p2_cons s s' s''_cons next tail ih =>
      have ih := ih step2
      have next_step := SmallStep.ss_seq2 p1 p2 p2_cons s s' next
      exact SmallStepSequence.cons (IMPProgram.seq p1 p2) (IMPProgram.seq p2_cons p2) s s' s'' next_step ih
