import LeanIMP.Basic

def factorialProgram : IMPProgram :=
  IMPProgram.seq (IMPProgram.assign "n" (NatExpr.const 3)) -- n := 3
  (IMPProgram.seq (IMPProgram.assign "result" (NatExpr.const 1)) -- result := 1
    (IMPProgram.«while» (BoolExpr.gt (NatExpr.var "n") (NatExpr.const 0)) -- while n > 0
      (IMPProgram.seq (IMPProgram.assign "result" (NatExpr.mul (NatExpr.var "result") (NatExpr.var "n"))) -- result := result * n
           (IMPProgram.assign "n" (NatExpr.sub (NatExpr.var "n") (NatExpr.const 1))) -- n := n - 1
      )
    )
  )

#eval (factorialProgram.runPartial []).lookup "result"


def whileLoopBase  : IMPProgram :=
  (IMPProgram.«while»
        (BoolExpr.gt (NatExpr.var "x") (NatExpr.const (0))) -- condition: x > 0
        (IMPProgram.assign "x" (NatExpr.sub (NatExpr.var "x") (NatExpr.const 1))) -- body: x := x - 1
      )

def whileLoopProgram (N_val: Nat) : IMPProgram :=
  (IMPProgram.seq
    (IMPProgram.assign "x" (NatExpr.const N_val)) -- x := N
    (whileLoopBase)
  )


#eval ((whileLoopProgram 1000).runPartial []).lookup "x"


def whileLoopBase2 (N_val: Nat) : IMPProgram :=
  (IMPProgram.«while»
        (BoolExpr.lt (NatExpr.var "x") (NatExpr.const (N_val))) -- condition: x < N
        (IMPProgram.assign "x" (NatExpr.add (NatExpr.var "x") (NatExpr.const 1))) -- body: x := x + 1
      )

def whileLoopProgram2 (N_val: Nat) : IMPProgram :=
  (IMPProgram.seq
    (IMPProgram.assign "x" (NatExpr.const 0)) -- x := 0
    (whileLoopBase2 N_val)
  )


#eval ((whileLoopProgram 1000).runPartial []).lookup "x"
