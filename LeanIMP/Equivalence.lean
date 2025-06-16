import LeanIMP.Basic
import LeanIMP.BigStepBasic
import LeanIMP.BigStep
import LeanIMP.SmallStepBasic
import LeanIMP.SmallStep

theorem big_step_implies_small_step {α: Type} [BEq α] {p: IMPProgram α} {s s': IMPState α}
  (big_step : BigStep p s s') :
  ∃k: Nat, SmallStepSequence p s s' k :=
  by
    induction big_step with
    | bs_skip s =>
      exists 1
      exact SmallStepSequence.single IMPProgram.skip s s (SmallStep.ss_skip s)
    | bs_assign x e s val eval =>
      exists 1
      exact SmallStepSequence.single (IMPProgram.assign x e) s (s.update x val) (SmallStep.ss_assign x e s val eval)
    | bs_seq p1 p2 s s1 s2 p1_ass p2_ass p1_ih p2_ih =>
      let ⟨k1, p1_ih⟩ := p1_ih
      let ⟨k2, p2_ih⟩ := p2_ih
      exists (k1 + k2)
      exact small_step_sequence_composeable p1_ih p2_ih
    | bs_if_true b_expr p_then p_else s s' eval p_then_tree p_then_ih =>
      have if_step := SmallStep.ss_if_true b_expr p_then p_else s eval
      let ⟨k1, p_then_ih⟩ := p_then_ih
      exists (1 + k1)
      exact SmallStepSequence.cons (IMPProgram.«if» b_expr p_then p_else) p_then s s s' k1 if_step p_then_ih
    | bs_if_false b_expr p_then p_else s s' eval p_then_tree p_else_ih =>
      have if_step := SmallStep.ss_if_false b_expr p_then p_else s eval
      let ⟨k1, p_else_ih⟩ := p_else_ih
      exists (1 + k1)
      exact SmallStepSequence.cons (IMPProgram.«if» b_expr p_then p_else) p_else s s s' k1 if_step p_else_ih
    | bs_while_true b_expr p_body s s1 s2 eval p_body_tree while_continues_tree p_body_ih while_continues_ih =>
      let ⟨k_body, p_body_ih⟩ := p_body_ih
      let ⟨k_continues, while_continues_ih⟩ := while_continues_ih
      refine ⟨(1 + (1 + (k_body + k_continues))), SmallStepSequence.cons (IMPProgram.«while» b_expr p_body) (IMPProgram.«if» b_expr (IMPProgram.seq (p_body) (IMPProgram.«while» b_expr p_body)) IMPProgram.skip) s s s2 (1 + (k_body + k_continues)) ?_ ?_⟩
      exact SmallStep.ss_while b_expr p_body s
      refine SmallStepSequence.cons (IMPProgram.«if» b_expr (IMPProgram.seq (p_body) (IMPProgram.«while» b_expr p_body)) IMPProgram.skip) (IMPProgram.seq (p_body) (IMPProgram.«while» b_expr p_body)) s s s2 (k_body + k_continues) ?_ ?_
      exact SmallStep.ss_if_true b_expr (IMPProgram.seq (p_body) (IMPProgram.«while» b_expr p_body)) (IMPProgram.skip) s eval
      refine small_step_sequence_composeable ?_ while_continues_ih
      exact p_body_ih
    | bs_while_false b_expr p_body s eval =>
      exists 3
      refine SmallStepSequence.cons (IMPProgram.«while» b_expr p_body) (IMPProgram.«if» b_expr (IMPProgram.seq (p_body) (IMPProgram.«while» b_expr p_body)) IMPProgram.skip) s s s 2 ?_ ?_
      exact SmallStep.ss_while b_expr p_body s
      refine SmallStepSequence.cons (IMPProgram.«if» b_expr (IMPProgram.seq (p_body) (IMPProgram.«while» b_expr p_body)) IMPProgram.skip) (IMPProgram.skip) s s s 1 ?_ ?_
      exact SmallStep.ss_if_false b_expr (IMPProgram.seq (p_body) (IMPProgram.«while» b_expr p_body)) IMPProgram.skip s eval
      exact SmallStepSequence.single IMPProgram.skip s s (SmallStep.ss_skip s)





theorem small_step_implies_big_step {α: Type} [BEq α] {p: IMPProgram α} {s s': IMPState α}
  (small_step : ∃k: Nat, SmallStepSequence p s s' k) :
  BigStep p s s' :=
  by
    obtain ⟨k, small_step⟩ := small_step
    revert small_step
    revert s s' p
    refine strong_induction_on (fun x => ∀{p: IMPProgram α}, ∀{s s': IMPState α}, SmallStepSequence p s s' x -> BigStep p s s') k ?_
    simp
    intros n
    intros ih
    intros p
    intros s s'
    intros small_step
    let small_step2 := small_step
    cases small_step with
      | single p s s' tree =>
        match tree with
          | SmallStep.ss_skip s => exact BigStep.bs_skip s
          | SmallStep.ss_assign x e s val eval => exact BigStep.bs_assign x e s val eval
      | cons p1 p2 s_ s'_ s''_ k_ tree rest =>
        cases tree with
          | ss_seq1 p1 p2 s__ s'__ ih_finished =>
            refine BigStep.bs_seq p1 p2 s s'_ s' ?_ ?_
            have k_gt_zero : k_ > 0 := small_step_sequence_gt_zero rest
            have zero_lt_k : 0 < k_ := by exact k_gt_zero
            have one_less : 1 < 1 + k_ := by
              rw [Nat.add_comm]
              apply Nat.succ_lt_succ
              exact zero_lt_k
            exact ih 1 one_less (SmallStepSequence.single p1 s s'_ ih_finished)
            have k_less : k_ < 1 + k_ := by
              rw [Nat.add_comm]
              exact Nat.lt_add_one k_
            exact ih k_ k_less rest
          | ss_seq2 p1 p2 p3 s__ s'__ ih_unfinished =>
            have ⟨k1_, k2_, inbetween, ⟨⟨step1, step2⟩, arith⟩⟩ := small_step_sequence_seperable (1 + k_) p1 p2 s s' small_step2
            have k1_gt_zero : k1_ > 0 := small_step_sequence_gt_zero step1
            have k2_gt_zero : k2_ > 0 := small_step_sequence_gt_zero step2
            have k1_lt_1_plus_k_ : k1_ < 1 + k_ := by
              rw [<- arith]
              refine Nat.lt_add_of_pos_right ?_
              exact k2_gt_zero
            have k2_lt_1_plus_k_ : k2_ < 1 + k_ := by
              rw [<- arith]
              rw [Nat.add_comm]
              refine Nat.lt_add_of_pos_right ?_
              exact k1_gt_zero

            have step1_ih := ih k1_ k1_lt_1_plus_k_ step1
            have step2_ih := ih k2_ k2_lt_1_plus_k_ step2
            exact
              BigStep.bs_seq p1 p2 s inbetween s' (ih k1_ k1_lt_1_plus_k_ step1)
                step2_ih

          | ss_if_true b_expr p2 p_else s eval =>
            have k_less : k_ < 1 + k_ := by
              rw [Nat.add_comm]
              exact Nat.lt_add_one k_
            refine BigStep.bs_if_true b_expr p2 p_else s s' eval ?subtree
            exact ih k_ k_less rest

          | ss_if_false b_expr pthen p2 s eval =>
            have k_less : k_ < 1 + k_ := by
              rw [Nat.add_comm]
              exact Nat.lt_add_one k_
            refine BigStep.bs_if_false b_expr pthen p2 s s' eval ?subtree2
            exact ih k_ k_less rest

          | ss_while b_expr pbody s =>
            have k_less : k_ < 1 + k_ := by
              rw [Nat.add_comm]
              exact Nat.lt_add_one k_
            have rest_tree := ih k_ k_less rest
            cases eval_bool: ((evalBoolExpr b_expr) s).fst with
              | true =>
                let rest_tree2 := rest_tree
                cases rest_tree with
                  | bs_if_true b_expr pthen pelse s s' eval_bs body_tree =>
                    have pure := IMPState.eval_bool_is_pure s b_expr
                    conv at eval_bool =>
                      unfold StateT.run
                    rw [eval_bool] at pure
                    cases body_tree with
                      | bs_seq p1 p2 s s1 s2 body_step rest_step =>
                        refine BigStep.bs_while_true b_expr pbody s ?inbetween s' pure ?body ?next_loop
                        exact s1
                        exact body_step
                        exact rest_step
                  | bs_if_false _ _ _ _ _ eval_bs =>
                    have eval_bs := by
                      exact congrArg Prod.fst eval_bs
                    simp at eval_bs
                    rw [eval_bool] at eval_bs
                    contradiction
              | false =>
                cases rest_tree with
                  | bs_if_true _ _ _ _ _ eval_bs =>
                    have eval_bs := by
                      exact congrArg Prod.fst eval_bs
                    simp at eval_bs
                    rw [eval_bool] at eval_bs
                    contradiction
                  | bs_if_false b_expr pthen pelse s s' eval subtree =>
                    cases subtree with
                    | bs_skip s_new => exact BigStep.bs_while_false b_expr pbody s eval
