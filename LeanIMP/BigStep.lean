import LeanIMP.Basic
import LeanIMP.Programs
import LeanIMP.BigStepBasic
import LeanIMP.IMPState
import Canonical

open BigStep

def IMPProgram.big_step_ext_eq {α: Type} [BEq α] (p1 p2 : IMPProgram α) : Prop :=
  forall (s : IMPState α),
  (forall (s_end1 : IMPState α), BigStep p1 s s_end1 -> (exists s_end2 : IMPState α, And (IMPState.ext_eq s_end1 s_end2) (BigStep p2 s s_end2)))
  ∧
  (forall (s_end2 : IMPState α), BigStep p2 s s_end2 -> (exists s_end1 : IMPState α, And (IMPState.ext_eq s_end2 s_end1) (BigStep p1 s s_end1)))



theorem IMPProgram.big_step_ext_eq_reflexive {α: Type} [BEq α] (p : IMPProgram α) : IMPProgram.big_step_ext_eq p p :=
  by
    intro s
    apply And.intro
    -- case 1
    intros s_end1
    intros h
    exists s_end1
    apply And.intro
    exact (IMPState.ext_eq_reflexive s_end1)
    exact h
    -- case 2
    intros s_end2
    intros h
    exists s_end2
    apply And.intro
    exact (IMPState.ext_eq_reflexive s_end2)
    exact h

theorem IMPProgram.big_step_ext_eq_symmetric {α: Type} [BEq α] {p1 p2 : IMPProgram α} : (IMPProgram.big_step_ext_eq p1 p2) -> (IMPProgram.big_step_ext_eq p2 p1)  :=
  by
    unfold IMPProgram.big_step_ext_eq
    intros h
    intros s
    let h_temp := h s
    apply And.intro
    exact h_temp.right
    exact h_temp.left

theorem IMPProgram.big_step_ext_eq_transitive {α: Type} [BEq α] {p1 p2 p3 : IMPProgram α} : (IMPProgram.big_step_ext_eq p1 p2) -> (IMPProgram.big_step_ext_eq p2 p3) -> (IMPProgram.big_step_ext_eq p1 p3)  :=
  by
    unfold IMPProgram.big_step_ext_eq
    intros h12 h23
    intros s
    apply And.intro
    -- case 1
    intros s_end1
    intros h_temp
    let h2_exists := (((h12 s).left s_end1 h_temp))
    rcases h2_exists with ⟨w, pw⟩
    let h2 := pw.right
    let h3_exists := (h23 s).left w h2
    rcases h3_exists with ⟨w2, pw2⟩
    exists w2
    apply And.intro
    exact (IMPState.ext_eq_transitive pw.left pw2.left)
    exact (pw2.right)
    -- case 2
    intros s_end2
    intros h_temp
    let h2_exists := (((h23 s).right s_end2 h_temp))
    rcases h2_exists with ⟨w, pw⟩
    let h2 := pw.right
    let h1_exists := (h12 s).right w h2
    rcases h1_exists with ⟨w2, pw2⟩
    exists w2
    apply And.intro
    exact (IMPState.ext_eq_transitive pw.left pw2.left)
    exact (pw2.right)


instance IMPProgramEquivalence {α: Type} [beq: BEq α] : Equivalence (@IMPProgram.big_step_ext_eq α beq) where
  refl := IMPProgram.big_step_ext_eq_reflexive
  symm := IMPProgram.big_step_ext_eq_symmetric
  trans := IMPProgram.big_step_ext_eq_transitive

instance IMPProgramSetoid (α: Type) [BEq α] : Setoid (IMPProgram α) where
  r := IMPProgram.big_step_ext_eq
  iseqv := IMPProgramEquivalence

def IMPProgramQ (α: Type) [BEq α] := Quotient (IMPProgramSetoid α)


macro "simp_monad_and_expr" : tactic =>
  `(tactic| simp [Bind.bind, Monad.toBind, StateT.pure, StateT.run, StateT.instMonad, StateT.bind, StateT.map, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run, evalBoolExpr, evalNatExpr])


theorem assigning_sets_value {α: Type} [BEq α] [ReflBEq α] (x: α) (s s_final: IMPState α) (N: Nat) :
  BigStep ((IMPProgram.assign x (NatExpr.const N))) s s_final ->
  s_final.lookup x = some N :=
    by
      intros h_big_step
      cases h_big_step with
      | bs_assign _ _ _ val assign_run =>
        conv at assign_run =>
            simp [Bind.bind, Monad.toBind, StateT.pure, StateT.run, StateT.instMonad, StateT.bind, StateT.map, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run, evalBoolExpr, evalNatExpr]
        injection assign_run with val_is_N _
        unfold IMPState.update
        unfold List.lookup
        rw [BEq.rfl]
        simp
        symm
        exact val_is_N

theorem decide_iff (p : Prop) [d : Decidable p] : decide p = true ↔ p := by simp
theorem bool_iff_false {b : Bool} : ¬b ↔ b = false := by cases b <;> exact by decide
theorem decide_false_iff (p : Prop) [Decidable p] : decide p = false ↔ ¬p :=
  bool_iff_false.symm.trans (not_congr (decide_iff _))
theorem of_decide_true {p : Prop} [Decidable p] : decide p → p :=
  (decide_iff p).1
theorem of_decide_false {p : Prop} [Decidable p] : decide p = false → ¬p :=
  (decide_false_iff p).1


theorem assigning_minus_one {α: Type} [BEq α] [ReflBEq α] (x: α) (s s_final: IMPState α) (N: Nat) :
  s.lookup x = some N ->
  BigStep ((IMPProgram.assign x (NatExpr.sub (NatExpr.var x) (NatExpr.const 1)))) s s_final ->
  s_final.lookup x = some (N-1) :=
    by
      intros prev_value
      intros h_big_step
      cases h_big_step with
      | bs_assign _ _ _ val assign_run =>
        conv at assign_run =>
            simp [Bind.bind, Monad.toBind, StateT.pure, StateT.run, StateT.instMonad, StateT.bind, StateT.map, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run, evalBoolExpr, evalNatExpr]
            rw [prev_value]
            simp [Bind.bind, Monad.toBind, StateT.pure, StateT.run, StateT.instMonad, StateT.bind, StateT.map, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run, evalBoolExpr, evalNatExpr]
        injection assign_run with val_is_N _
        unfold IMPState.update
        unfold List.lookup
        simp
        symm
        exact val_is_N

theorem assigning_plus_one {α: Type} [BEq α] [ReflBEq α] (x: α) (s s_final: IMPState α) (N: Nat) :
  s.lookup x = some N ->
  BigStep ((IMPProgram.assign x (NatExpr.add (NatExpr.var x) (NatExpr.const 1)))) s s_final ->
  s_final.lookup x = some (N+1) :=
    by
      intros prev_value
      intros h_big_step
      cases h_big_step with
      | bs_assign _ _ _ val assign_run =>
        conv at assign_run =>
            simp [Bind.bind, Monad.toBind, StateT.pure, StateT.run, StateT.instMonad, StateT.bind, StateT.map, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run, evalBoolExpr, evalNatExpr]
            rw [prev_value]
            simp [Bind.bind, Monad.toBind, StateT.pure, StateT.run, StateT.instMonad, StateT.bind, StateT.map, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run, evalBoolExpr, evalNatExpr]
        injection assign_run with val_is_N _
        unfold IMPState.update
        unfold List.lookup
        simp
        symm
        exact val_is_N

theorem whileLoopBase_terminates_at_zero (N_val : Nat) (s s_final : IMPState Identifier) :
  s.lookup Identifier.x = some N_val ->
  BigStep (whileLoopBase) s s_final ->
  s_final.lookup Identifier.x = some 0 :=
    by
      intros x_is_N_val
      intros h_big_step
      cases h_big_step with
        | bs_while_false _ _ _ h_not_greater =>
          conv at h_not_greater =>
            simp [Bind.bind, Monad.toBind, StateT.pure, StateT.run, StateT.instMonad, StateT.bind, StateT.map, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run, evalBoolExpr, evalNatExpr]
            rw [x_is_N_val]
            simp [Bind.bind, Monad.toBind, StateT.pure, StateT.run, StateT.instMonad, StateT.bind, StateT.map, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run, evalBoolExpr, evalNatExpr]
          injection h_not_greater with is_leq _
          have is_leq : ¬ (0 < N_val) := of_decide_false is_leq
          have is_leq : (0 >= N_val) := Nat.ge_of_not_lt is_leq
          have is_zero : (N_val = 0) := Nat.eq_zero_of_le_zero is_leq
          rw [is_zero] at x_is_N_val
          exact x_is_N_val
        | bs_while_true _ _ _ mid2 _ h_greater h_body h_next_while =>
          conv at h_greater =>
            simp [Bind.bind, Monad.toBind, StateT.pure, StateT.run, StateT.instMonad, StateT.bind, StateT.map, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run, evalBoolExpr, evalNatExpr]
            rw [x_is_N_val]
            simp [Bind.bind, Monad.toBind, StateT.pure, StateT.run, StateT.instMonad, StateT.bind, StateT.map, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run, evalBoolExpr, evalNatExpr]
          injection h_greater with is_lt _
          have is_lt : (0 < N_val) := of_decide_true is_lt

          have mid2_is_minus_one : mid2.lookup Identifier.x = some (N_val - 1) := assigning_minus_one Identifier.x s mid2 N_val x_is_N_val h_body
          exact (whileLoopBase_terminates_at_zero (N_val - 1) mid2 s_final (mid2_is_minus_one) (h_next_while))



theorem whileLoop_terminates_at_zero (N_val : Nat) (s_final : IMPState Identifier) :
  BigStep (whileLoopProgram N_val) [] s_final ->
  s_final.lookup Identifier.x = some 0 :=
    by
      intros h_big_step
      cases h_big_step with
        | bs_seq _ _ _ mid s' h_bs_assign h_bs_while =>
          have mid_x_is_N : mid.lookup Identifier.x = some N_val := assigning_sets_value Identifier.x [] mid N_val h_bs_assign
          clear h_bs_assign
          exact (whileLoopBase_terminates_at_zero N_val mid s_final mid_x_is_N h_bs_while)


def whileLoopBaseExists (s: IMPState Identifier) (N_val: Nat) :
  s.lookup Identifier.x = N_val ->
  Σ' s_final : IMPState Identifier, (BigStep (whileLoopBase) s s_final) :=
    by
      intros x_is_N_val
      cases N_val with
        | zero =>
          refine ⟨?_, ?_⟩
          rotate_left
          unfold whileLoopBase
          refine bs_while_false (BoolExpr.gt (NatExpr.var Identifier.x) (NatExpr.const (0))) ?_ ?_ ?_
          simp_monad_and_expr
          rw [x_is_N_val]
          simp_monad_and_expr
        | succ n =>
          have s_mid_update : (s.update Identifier.x n).lookup Identifier.x = n := by
            unfold IMPState.update
            eq_refl
          let ih := whileLoopBaseExists (s.update Identifier.x n) n s_mid_update
          refine ⟨?_, ?_⟩
          rotate_left
          refine bs_while_true (BoolExpr.gt (NatExpr.var Identifier.x) (NatExpr.const (0))) ?_ ?_ ?_ ?_ ?_ ?_ ?_
          rotate_left
          simp_monad_and_expr
          rw [x_is_N_val]
          simp_monad_and_expr
          refine bs_assign Identifier.x ?_ ?_ ?_ ?_
          exact n
          simp_monad_and_expr
          rw [x_is_N_val]
          simp_monad_and_expr
          rw [<- whileLoopBase]
          rotate_left
          exact ih.fst
          exact ih.snd

def whileLoopBigStepExists (N_val : Nat) :
  Σ' s_final : IMPState Identifier, (BigStep (whileLoopProgram N_val) [] s_final) :=
    by
      let prog_assign := IMPProgram.assign Identifier.x (NatExpr.const N_val)
      let prog_while := whileLoopBase
      have x_is_N_val : [(Identifier.x, N_val)].lookup Identifier.x = N_val := by
        unfold List.lookup
        simp
      let baseLoop := whileLoopBaseExists [(Identifier.x, N_val)] N_val x_is_N_val
      refine ⟨?_, ?_⟩
      rotate_left
      unfold whileLoopProgram
      refine bs_seq (IMPProgram.assign Identifier.x (NatExpr.const N_val)) ?_ ?_ ?_ ?_ ?_ ?_
      exact [(Identifier.x, N_val)]
      refine bs_assign Identifier.x ?_ ?_ ?_ ?_
      simp_monad_and_expr
      rotate_left
      exact baseLoop.fst
      exact baseLoop.snd


#eval (whileLoopBigStepExists 3).fst


instance (α: Type) [BEq α] [Inhabited (IMPState α)] (p: IMPProgram α) (s_start: IMPState α) : Inhabited (Σ' s_final : IMPState α, BigStep p s_start s_final) where
  default := ⟨s_start, sorry⟩


unsafe def runBigStep {α: Type} [inh: Inhabited α] [beq : BEq α] (p: IMPProgram α) (s_start: IMPState α) :
  Σ' s_final : IMPState α, BigStep p s_start s_final :=
    by
      match p with
        | IMPProgram.skip => exact ⟨s_start, BigStep.bs_skip s_start⟩
        | IMPProgram.assign x expr =>
          let next := (evalNatExpr expr).run s_start
          let next_val := next.fst
          let next_state := s_start.update x next_val
          have next_is_next : (evalNatExpr expr).run s_start = (next_val, s_start) := by
            simp_monad
            rw [IMPState.eval_int_is_pure]
            rfl
          refine ⟨?s_final, ?_⟩
          exact next_state
          have h := BigStep.bs_assign x expr s_start next_val next_is_next
          simp [next_state] at h
          exact h

        | IMPProgram.seq p1 p2 =>
          let ⟨s1, bs1⟩ := runBigStep p1 s_start
          let ⟨s2, bs2⟩ := runBigStep p2 s1
          exact ⟨s2, BigStep.bs_seq p1 p2 s_start s1 s2 bs1 bs2⟩

        | IMPProgram.«if» bexpr if_body else_body =>
          match h : evalBoolExpr bexpr s_start with
            | (true, s) =>
              rw [IMPState.eval_bool_is_pure] at h
              let next := (evalBoolExpr bexpr).run s_start
              have next_is_next : (evalBoolExpr bexpr).run s_start = (true, s_start) := by
                simp_monad
                rw [IMPState.eval_bool_is_pure]
                injection h with h1 h2
                congr
              let ⟨s_if, bs_if⟩ := runBigStep if_body s_start
              exact ⟨s_if, BigStep.bs_if_true bexpr if_body else_body s_start s_if next_is_next bs_if⟩

            | (false, s) =>
              rw [IMPState.eval_bool_is_pure] at h
              let next := (evalBoolExpr bexpr).run s_start
              have next_is_next : (evalBoolExpr bexpr).run s_start = (false, s_start) := by
                simp_monad
                rw [IMPState.eval_bool_is_pure]
                injection h with h1 h2
                congr
              let ⟨s_if, bs_if⟩ := runBigStep else_body s_start
              exact ⟨s_if, BigStep.bs_if_false bexpr if_body else_body s_start s_if next_is_next bs_if⟩

        | IMPProgram.«while» bexpr body =>
          match h : evalBoolExpr bexpr s_start with
            | (true, s) =>
              rw [IMPState.eval_bool_is_pure] at h
              let next := (evalBoolExpr bexpr).run s_start
              have next_is_next : (evalBoolExpr bexpr).run s_start = (true, s_start) := by
                simp_monad
                rw [IMPState.eval_bool_is_pure]
                injection h with h1 h2
                congr
              let ⟨s_body, bs_body⟩ := runBigStep body s_start
              let ⟨s_next, bs_next⟩ := runBigStep (IMPProgram.«while» bexpr body) s_body
              exact ⟨s_next, BigStep.bs_while_true bexpr body s_start s_body s_next next_is_next bs_body bs_next⟩
            | (false, s) =>
              rw [IMPState.eval_bool_is_pure] at h
              let next := (evalBoolExpr bexpr).run s_start
              have next_is_next : (evalBoolExpr bexpr).run s_start = (false, s_start) := by
                simp_monad
                rw [IMPState.eval_bool_is_pure]
                injection h with h1 h2
                congr
              exact ⟨s_start, BigStep.bs_while_false bexpr body s_start next_is_next⟩
decreasing_by all_goals sorry


#eval! (runBigStep (whileLoopProgram2 10) []).fst
