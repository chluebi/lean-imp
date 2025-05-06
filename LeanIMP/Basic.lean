
abbrev IMPState : Type := (List (String × Nat))

def IMPState.update (s: IMPState) (key: String) (value: Nat) :=
  (key, value) :: s

def IMPState.prepend_updates (s1 s2: IMPState) :=
  List.foldr (fun (k, v) l  => IMPState.update l k v) s1 s2


def IMPState.does_not_contain (s: IMPState) (k: String) : Prop :=
  match s with
  | List.nil => True
  | (a, _)::as => And (Not (a = k)) (IMPState.does_not_contain as k)

abbrev IMPComputation (α : Type) : Type := StateM IMPState α

def addPair (key: String) (value: Nat) : IMPComputation Unit := do
  let s ← get
  set (s.update key value)


inductive NatExpr where
  | var (_:String)
  | const (_:Nat)
  | add (_ _: NatExpr)
  | sub (_ _: NatExpr)
  | mul (_ _: NatExpr)

def NatExpr.does_not_contain (expr: NatExpr) (s: String) : Prop :=
  match expr with
    | var (v:String) => !(v = s)
    | const (_:Nat) => True
    | add (x : NatExpr) (y: NatExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | sub (x : NatExpr) (y: NatExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | mul (x : NatExpr) (y: NatExpr) => And (x.does_not_contain s) (y.does_not_contain s)


inductive BoolExpr where
  | var (_:String)
  | const (_:Bool)
  | eq (_ _: NatExpr)
  | neq (_ _: NatExpr)
  | lt (_ _: NatExpr)
  | leq (_ _: NatExpr)
  | gt (_ _: NatExpr)
  | geq (_ _: NatExpr)
  | or (_ _: BoolExpr)
  | and (_ _: BoolExpr)
  | not (_: BoolExpr)

def BoolExpr.does_not_contain (expr: BoolExpr) (s: String) : Prop :=
  match expr with
    | var (v:String) => !(v = s)
    | const (_:Bool) => True
    | eq (x : NatExpr) (y : NatExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | neq (x : NatExpr) (y: NatExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | lt (x : NatExpr) (y: NatExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | leq (x : NatExpr) (y: NatExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | gt (x : NatExpr) (y: NatExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | geq (x : NatExpr) (y: NatExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | or (x : BoolExpr) (y: BoolExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | and (x : BoolExpr) (y: BoolExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | not (x : BoolExpr) => x.does_not_contain s


inductive IMPProgram where
  | skip
  | assign (var: String) (expr: NatExpr)
  | seq (_ _: IMPProgram)
  | «if» (_: BoolExpr) (_ _: IMPProgram)
  | «while» (_: BoolExpr) (_: IMPProgram)


def evalNatExpr : NatExpr → IMPComputation Nat
  | NatExpr.var varName => do
    let s ← get
    match s.lookup varName with
    | some value => pure value
    | none => pure 0
  | NatExpr.const n => pure n
  | NatExpr.add e1 e2 => do
    let n1 ← evalNatExpr e1
    let n2 ← evalNatExpr e2
    pure (n1 + n2)
  | NatExpr.sub e1 e2 => do
    let n1 ← evalNatExpr e1
    let n2 ← evalNatExpr e2
    pure (n1 - n2)
  | NatExpr.mul e1 e2 => do
    let n1 ← evalNatExpr e1
    let n2 ← evalNatExpr e2
    pure (n1 * n2)

def evalBoolExpr : BoolExpr → IMPComputation Bool
  | BoolExpr.var varName => do
    let s ← get
    match s.lookup varName with
    | some 0 => pure false
    | some _ => pure true
    | none => pure true
  | BoolExpr.const b => pure b
  | BoolExpr.eq e1 e2 => do
    let n1 ← evalNatExpr e1
    let n2 ← evalNatExpr e2
    pure (n1 == n2)
  | BoolExpr.neq e1 e2 => do
    let n1 ← evalNatExpr e1
    let n2 ← evalNatExpr e2
    pure (n1 != n2)
  | BoolExpr.lt e1 e2 => do
    let n1 ← evalNatExpr e1
    let n2 ← evalNatExpr e2
    pure (decide (n1 < n2))
  | BoolExpr.leq e1 e2 => do
    let n1 ← evalNatExpr e1
    let n2 ← evalNatExpr e2
    pure (decide (n1 ≤ n2))
  | BoolExpr.gt e1 e2 => do
    let n1 ← evalNatExpr e1
    let n2 ← evalNatExpr e2
    pure (decide (n1 > n2))
  | BoolExpr.geq e1 e2 => do
    let n1 ← evalNatExpr e1
    let n2 ← evalNatExpr e2
    pure (decide (n1 ≥ n2))
  | BoolExpr.or b1 b2 => do
    let res1 ← evalBoolExpr b1
    if res1 then pure true else evalBoolExpr b2
  | BoolExpr.and b1 b2 => do
    let res1 ← evalBoolExpr b1
    if res1 then evalBoolExpr b2 else pure false
  | BoolExpr.not b => do
    let res ← evalBoolExpr b
    pure (!res)

def IMPProgram.runProgram : IMPProgram → IMPComputation Unit
  | IMPProgram.skip => pure ()
  | IMPProgram.assign varName expr => do
    let value ← evalNatExpr expr
    addPair varName value
  | IMPProgram.seq p1 p2 => do
    runProgram p1
    runProgram p2
  | IMPProgram.«if» cond thenP elseP => do
    let condition ← evalBoolExpr cond
    if condition then
      runProgram thenP
    else
      runProgram elseP
  | IMPProgram.«while» cond body => do
    let condition ← evalBoolExpr cond
    if (condition) then
      runProgram body
      runProgram (IMPProgram.«while» cond body)
decreasing_by all_goals sorry

partial def IMPProgram.runProgramPartial : IMPProgram → IMPComputation Unit
  | IMPProgram.skip => pure ()
  | IMPProgram.assign varName expr => do
    let value ← evalNatExpr expr
    addPair varName value
  | IMPProgram.seq p1 p2 => do
    runProgramPartial p1
    runProgramPartial p2
  | IMPProgram.«if» cond thenP elseP => do
    let condition ← evalBoolExpr cond
    if condition then
      runProgramPartial thenP
    else
      runProgramPartial elseP
  | IMPProgram.«while» cond body => do
    let condition ← evalBoolExpr cond
    unless (not condition) do
      runProgramPartial body
      runProgramPartial (IMPProgram.«while» cond body)


def IMPProgram.run (program: IMPProgram) (state: IMPState) :=
  let (_, state) := (runProgram program).run state |>.run
  state

def IMPProgram.runPartial (program: IMPProgram) (state: IMPState) :=
  let (_, state) := (runProgramPartial program).run state |>.run
  state

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


def whileLoopBase (N_val: Nat) : IMPProgram :=
  (IMPProgram.«while»
        (BoolExpr.lt (NatExpr.var "x") (NatExpr.const (N_val))) -- condition: x < N
        (IMPProgram.assign "x" (NatExpr.add (NatExpr.var "x") (NatExpr.const 1))) -- body: x := x + 1
      )

def whileLoopProgram (N_val: Nat) : IMPProgram :=
  (IMPProgram.seq
    (IMPProgram.assign "x" (NatExpr.const 0)) -- x := 0
    (whileLoopBase N_val)
  )


#eval ((whileLoopProgram 1000).runPartial []).lookup "x"

#reduce evalNatExpr (NatExpr.const (1)) []
