import LeanIMP.Basic
import LeanIMP.Programs
import LeanIMP.BigStepBasic
import LeanIMP.IMPState

open BigStep

def IMPProgram.big_step_ext_eq (p1 p2 : IMPProgram) : Prop :=
  forall (s : IMPState),
  (forall (s_end1 : IMPState), BigStep p1 s s_end1 -> (exists s_end2 : IMPState, And (IMPState.ext_eq s_end1 s_end2) (BigStep p2 s s_end2)))
  ∧
  (forall (s_end2 : IMPState), BigStep p2 s s_end2 -> (exists s_end1 : IMPState, And (IMPState.ext_eq s_end2 s_end1) (BigStep p1 s s_end1)))

theorem IMPProgram.big_step_ext_eq_reflexive (p : IMPProgram) : IMPProgram.big_step_ext_eq p p :=
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

theorem IMPProgram.big_step_ext_eq_symmetric {p1 p2 : IMPProgram} : (IMPProgram.big_step_ext_eq p1 p2) -> (IMPProgram.big_step_ext_eq p2 p1)  :=
  by
    unfold IMPProgram.big_step_ext_eq
    intros h
    intros s
    let h_temp := h s
    apply And.intro
    exact h_temp.right
    exact h_temp.left

theorem IMPProgram.big_step_ext_eq_transitive {p1 p2 p3 : IMPProgram} : (IMPProgram.big_step_ext_eq p1 p2) -> (IMPProgram.big_step_ext_eq p2 p3) -> (IMPProgram.big_step_ext_eq p1 p3)  :=
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


instance : Equivalence IMPProgram.big_step_ext_eq where
  refl := IMPProgram.big_step_ext_eq_reflexive
  symm := IMPProgram.big_step_ext_eq_symmetric
  trans := IMPProgram.big_step_ext_eq_transitive

macro "simp_monad_and_expr" : tactic =>
  `(tactic| simp [Bind.bind, Monad.toBind, StateT.pure, StateT.run, StateT.instMonad, StateT.bind, StateT.map, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run, evalBoolExpr, evalNatExpr])


theorem assigning_sets_value (x: String) (s s_final: IMPState) (N: Nat) :
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


theorem assigning_minus_one (x: String) (s s_final: IMPState) (N: Nat) :
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

theorem assigning_plus_one (x: String) (s s_final: IMPState) (N: Nat) :
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

theorem whileLoopBase_terminates_at_zero (N_val : Nat) (s s_final : IMPState) :
  s.lookup "x" = some N_val ->
  BigStep (whileLoopBase) s s_final ->
  s_final.lookup "x" = some 0 :=
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

          have mid2_is_minus_one : mid2.lookup "x" = some (N_val - 1) := assigning_minus_one "x" s mid2 N_val x_is_N_val h_body
          exact (whileLoopBase_terminates_at_zero (N_val - 1) mid2 s_final (mid2_is_minus_one) (h_next_while))



theorem whileLoop_terminates_at_zero (N_val : Nat) (s_final : IMPState) :
  BigStep (whileLoopProgram N_val) [] s_final ->
  s_final.lookup "x" = some 0 :=
    by
      intros h_big_step
      cases h_big_step with
        | bs_seq _ _ _ mid s' h_bs_assign h_bs_while =>
          have mid_x_is_N : mid.lookup "x" = some N_val := assigning_sets_value "x" [] mid N_val h_bs_assign
          clear h_bs_assign
          exact (whileLoopBase_terminates_at_zero N_val mid s_final mid_x_is_N h_bs_while)


def whileLoopBaseExists (s: IMPState) (N_val: Nat) :
  s.lookup "x" = N_val ->
  Σ' s_final : IMPState, (BigStep (whileLoopBase) s s_final) :=
    by
      intros x_is_N_val
      cases N_val with
        | zero =>
          refine ⟨?_, ?_⟩
          rotate_left
          unfold whileLoopBase
          refine bs_while_false ?_ ?_ ?_ ?_
          simp_monad_and_expr
          rw [x_is_N_val]
          simp_monad_and_expr
        | succ n =>
          have s_mid_update : (s.update "x" n).lookup "x" = n := by
            unfold IMPState.update
            eq_refl
          let ih := whileLoopBaseExists (s.update "x" n) n s_mid_update
          refine ⟨?_, ?_⟩
          rotate_left
          refine bs_while_true ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          rotate_left
          simp_monad_and_expr
          rw [x_is_N_val]
          simp_monad_and_expr
          refine bs_assign ?_ ?_ ?_ ?_ ?_
          exact n
          simp_monad_and_expr
          rw [x_is_N_val]
          simp_monad_and_expr
          rw [<- whileLoopBase]
          rotate_left
          exact ih.fst
          exact ih.snd

def whileLoopBigStepExists (N_val : Nat) :
  Σ' s_final : IMPState, (BigStep (whileLoopProgram N_val) [] s_final) :=
    by
      let prog_assign := IMPProgram.assign "x" (NatExpr.const N_val)
      let prog_while := whileLoopBase
      have x_is_N_val : [("x", N_val)].lookup "x" = N_val := by simp
      let baseLoop := whileLoopBaseExists [("x", N_val)] N_val x_is_N_val
      refine ⟨?_, ?_⟩
      rotate_left
      unfold whileLoopProgram
      refine bs_seq ?_ ?_ ?_ ?_ ?_ ?_ ?_
      exact [("x", N_val)]
      refine bs_assign ?_ ?_ ?_ ?_ ?_
      simp_monad_and_expr
      rotate_left
      exact baseLoop.fst
      exact baseLoop.snd


#eval (whileLoopBigStepExists 100).fst






theorem whileLoopBase2_terminates_at_N (N_val_current N_val : Nat) (s s_final : IMPState) :
  N_val_current <= N_val ->
  s.lookup "x" = some N_val_current ->
  BigStep (whileLoopBase2 N_val) s s_final ->
  s_final.lookup "x" = some N_val :=
    by
      intros N_val_current_less
      intros x_is_N_val
      intros h_big_step
      cases h_big_step with
        | bs_while_false _ _ _ h_not_less =>
          conv at h_not_less =>
            simp [Bind.bind, Monad.toBind, StateT.pure, StateT.run, StateT.instMonad, StateT.bind, StateT.map, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run, evalBoolExpr, evalNatExpr]
            rw [x_is_N_val]
            simp [Bind.bind, Monad.toBind, StateT.pure, StateT.run, StateT.instMonad, StateT.bind, StateT.map, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run, evalBoolExpr, evalNatExpr]
          injection h_not_less with is_leq _
          have is_leq : ¬ (N_val_current < N_val) := of_decide_false is_leq
          have is_leq : (N_val_current >= N_val) := Nat.ge_of_not_lt is_leq
          have is_eq : (N_val_current = N_val) := Nat.le_antisymm N_val_current_less is_leq
          rw [is_eq] at x_is_N_val
          exact x_is_N_val
        | bs_while_true _ _ _ mid2 _ h_less h_body h_next_while =>
          conv at h_less =>
            simp [Bind.bind, Monad.toBind, StateT.pure, StateT.run, StateT.instMonad, StateT.bind, StateT.map, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run, evalBoolExpr, evalNatExpr]
            rw [x_is_N_val]
            simp [Bind.bind, Monad.toBind, StateT.pure, StateT.run, StateT.instMonad, StateT.bind, StateT.map, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, Id.run, evalBoolExpr, evalNatExpr]
          injection h_less with is_lt _
          have is_lt : (N_val_current < N_val) := of_decide_true is_lt
          have is_leq : (1 + N_val_current <= N_val) := Nat.one_add_le_iff.mpr is_lt
          rw [Nat.add_comm] at is_leq

          have mid2_is_minus_one : mid2.lookup "x" = some (N_val_current + 1) := assigning_plus_one "x" s mid2 N_val_current x_is_N_val h_body
          exact (whileLoopBase2_terminates_at_N (N_val_current + 1) N_val mid2 s_final is_leq (mid2_is_minus_one) (h_next_while))



theorem whileLoop2_terminates_at_zero (N_val : Nat) (s_final : IMPState) :
  BigStep (whileLoopProgram2 N_val) [] s_final ->
  s_final.lookup "x" = some N_val :=
    by
      intros h_big_step
      cases h_big_step with
        | bs_seq _ _ _ mid s' h_bs_assign h_bs_while =>
          have mid_x_is_0 : mid.lookup "x" = some 0 := assigning_sets_value "x" [] mid 0 h_bs_assign
          have zero_leq_N : 0 <= N_val := Nat.zero_le N_val
          clear h_bs_assign
          exact (whileLoopBase2_terminates_at_N 0 N_val mid s_final zero_leq_N mid_x_is_0 h_bs_while)
