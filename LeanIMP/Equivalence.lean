import LeanIMP.Basic
import LeanIMP.BigStepBasic
import LeanIMP.BigStep
import LeanIMP.SmallStepBasic
import LeanIMP.SmallStep

theorem big_step_implies_small_step {α: Type} [BEq α] {p: IMPProgram α} {s s': IMPState α}
  (big_step : BigStep p s s') :
  SmallStepSequence p s s' :=
  by
    induction big_step with
    | bs_skip s => exact SmallStepSequence.single IMPProgram.skip s s (SmallStep.ss_skip s)
    | bs_assign x e s val eval => exact SmallStepSequence.single (IMPProgram.assign x e) s (s.update x val) (SmallStep.ss_assign x e s val eval)
    | bs_seq p1 p2 s s1 s2 p1_ass p2_ass p1_ih p2_ih =>
      exact small_step_sequence_composeable p1_ih p2_ih
    | bs_if_true b_expr p_then p_else s s' eval p_then_tree p_then_ih =>
      have if_step := SmallStep.ss_if_true b_expr p_then p_else s eval
      exact SmallStepSequence.cons (IMPProgram.«if» b_expr p_then p_else) p_then s s s' if_step p_then_ih
    | bs_if_false b_expr p_then p_else s s' eval p_then_tree p_else_ih =>
      have if_step := SmallStep.ss_if_false b_expr p_then p_else s eval
      exact SmallStepSequence.cons (IMPProgram.«if» b_expr p_then p_else) p_else s s s' if_step p_else_ih
    | bs_while_true b_expr p_body s s1 s2 eval p_body_tree while_continues_tree p_body_ih while_continues_ih =>
      refine SmallStepSequence.cons (IMPProgram.«while» b_expr p_body) (IMPProgram.«if» b_expr (IMPProgram.seq (p_body) (IMPProgram.«while» b_expr p_body)) IMPProgram.skip) s s s2 ?_ ?_
      exact SmallStep.ss_while b_expr p_body s s
      refine SmallStepSequence.cons (IMPProgram.«if» b_expr (IMPProgram.seq (p_body) (IMPProgram.«while» b_expr p_body)) IMPProgram.skip) (IMPProgram.seq (p_body) (IMPProgram.«while» b_expr p_body)) s s s2 ?_ ?_
      exact SmallStep.ss_if_true b_expr (IMPProgram.seq (p_body) (IMPProgram.«while» b_expr p_body)) (IMPProgram.skip) s eval
      refine small_step_sequence_composeable ?_ while_continues_ih
      exact p_body_ih
    | bs_while_false b_expr p_body s eval =>
      refine SmallStepSequence.cons (IMPProgram.«while» b_expr p_body) (IMPProgram.«if» b_expr (IMPProgram.seq (p_body) (IMPProgram.«while» b_expr p_body)) IMPProgram.skip) s s s ?_ ?_
      exact SmallStep.ss_while b_expr p_body s s
      refine SmallStepSequence.cons (IMPProgram.«if» b_expr (IMPProgram.seq (p_body) (IMPProgram.«while» b_expr p_body)) IMPProgram.skip) (IMPProgram.skip) s s s ?_ ?_
      exact SmallStep.ss_if_false b_expr (IMPProgram.seq (p_body) (IMPProgram.«while» b_expr p_body)) IMPProgram.skip s eval
      exact SmallStepSequence.single IMPProgram.skip s s (SmallStep.ss_skip s)
