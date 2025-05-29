import LeanIMP.Basic


inductive Identifier where
  | N
  | result
  | x
deriving BEq, Repr, Inhabited

instance : PartialEquivBEq Identifier where
  symm := by
    intro a b h_eq
    cases a <;> cases b
    case N.N => rfl
    case result.result => rfl
    case x.x => rfl
    all_goals (
      exact Bool.noConfusion h_eq
    )

  trans := by
    intro a b c h_ab h_bc
    cases a <;> cases b <;> cases c
    -- Correct branches:
    case N.N.N => rfl
    case result.result.result => rfl
    case x.x.x => rfl
    -- Everything else:
    all_goals (
      first
      | exact Bool.noConfusion h_ab
      | exact Bool.noConfusion h_bc
    )

instance : ReflBEq Identifier where
  rfl := by
    intro a
    cases a
    all_goals (
      rfl
    )


def factorialProgram : IMPProgram Identifier :=
  IMPProgram.seq (IMPProgram.assign Identifier.N (NatExpr.const 3)) -- n := 3
  (IMPProgram.seq (IMPProgram.assign Identifier.result (NatExpr.const 1)) -- result := 1
    (IMPProgram.«while» (BoolExpr.gt (NatExpr.var Identifier.N) (NatExpr.const 0)) -- while n > 0
      (IMPProgram.seq (IMPProgram.assign Identifier.result (NatExpr.mul (NatExpr.var Identifier.result) (NatExpr.var Identifier.N))) -- result := result * n
           (IMPProgram.assign Identifier.N (NatExpr.sub (NatExpr.var Identifier.N) (NatExpr.const 1))) -- n := n - 1
      )
    )
  )

#eval (factorialProgram.runPartial []).lookup Identifier.result


def whileLoopBase  : IMPProgram Identifier :=
  (IMPProgram.«while»
        (BoolExpr.gt (NatExpr.var Identifier.x) (NatExpr.const (0))) -- condition: x > 0
        (IMPProgram.assign Identifier.x (NatExpr.sub (NatExpr.var Identifier.x) (NatExpr.const 1))) -- body: x := x - 1
      )

def whileLoopProgram (N_val: Nat) : IMPProgram Identifier :=
  (IMPProgram.seq
    (IMPProgram.assign Identifier.x (NatExpr.const N_val)) -- x := N
    (whileLoopBase)
  )


#eval ((whileLoopProgram 1000).runPartial []).lookup Identifier.x


def whileLoopBase2 (N_val: Nat) : IMPProgram Identifier :=
  (IMPProgram.«while»
        (BoolExpr.lt (NatExpr.var Identifier.x) (NatExpr.const (N_val))) -- condition: x < N
        (IMPProgram.assign Identifier.x (NatExpr.add (NatExpr.var Identifier.x) (NatExpr.const 1))) -- body: x := x + 1
      )

def whileLoopProgram2 (N_val: Nat) : IMPProgram Identifier :=
  (IMPProgram.seq
    (IMPProgram.assign Identifier.x (NatExpr.const 0)) -- x := 0
    (whileLoopBase2 N_val)
  )


#eval ((whileLoopProgram 1000).runPartial []).lookup Identifier.x
