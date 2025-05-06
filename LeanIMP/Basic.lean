
abbrev IMPState : Type := (List (String × Int))

def IMPState.update (s: IMPState) (key: String) (value: Int) :=
  (key, value) :: s

def IMPState.prepend_updates (s1 s2: IMPState) :=
  List.foldr (fun (k, v) l  => IMPState.update l k v) s1 s2


def IMPState.does_not_contain (s: IMPState) (k: String) : Prop :=
  match s with
  | List.nil => True
  | (a, _)::as => And (Not (a = k)) (IMPState.does_not_contain as k)

abbrev IMPComputation (α : Type) : Type := StateM IMPState α

def addPair (key: String) (value: Int) : IMPComputation Unit := do
  let s ← get
  set (s.update key value)


inductive IntExpr where
  | var (_:String)
  | const (_:Int)
  | add (_ _: IntExpr)
  | sub (_ _: IntExpr)
  | mul (_ _: IntExpr)

def IntExpr.does_not_contain (expr: IntExpr) (s: String) : Prop :=
  match expr with
    | var (v:String) => !(v = s)
    | const (_:Int) => True
    | add (x : IntExpr) (y: IntExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | sub (x : IntExpr) (y: IntExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | mul (x : IntExpr) (y: IntExpr) => And (x.does_not_contain s) (y.does_not_contain s)


inductive BoolExpr where
  | var (_:String)
  | const (_:Bool)
  | eq (_ _: IntExpr)
  | neq (_ _: IntExpr)
  | lt (_ _: IntExpr)
  | leq (_ _: IntExpr)
  | gt (_ _: IntExpr)
  | geq (_ _: IntExpr)
  | or (_ _: BoolExpr)
  | and (_ _: BoolExpr)
  | not (_: BoolExpr)

def BoolExpr.does_not_contain (expr: BoolExpr) (s: String) : Prop :=
  match expr with
    | var (v:String) => !(v = s)
    | const (_:Bool) => True
    | eq (x : IntExpr) (y : IntExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | neq (x : IntExpr) (y: IntExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | lt (x : IntExpr) (y: IntExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | leq (x : IntExpr) (y: IntExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | gt (x : IntExpr) (y: IntExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | geq (x : IntExpr) (y: IntExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | or (x : BoolExpr) (y: BoolExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | and (x : BoolExpr) (y: BoolExpr) => And (x.does_not_contain s) (y.does_not_contain s)
    | not (x : BoolExpr) => x.does_not_contain s


inductive IMPProgram where
  | skip
  | assign (var: String) (expr: IntExpr)
  | seq (_ _: IMPProgram)
  | «if» (_: BoolExpr) (_ _: IMPProgram)
  | «while» (_: BoolExpr) (_: IMPProgram)


def evalIntExpr : IntExpr → IMPComputation Int
  | IntExpr.var varName => do
    let s ← get
    match s.lookup varName with
    | some value => pure value
    | none => pure 0
  | IntExpr.const n => pure n
  | IntExpr.add e1 e2 => do
    let n1 ← evalIntExpr e1
    let n2 ← evalIntExpr e2
    pure (n1 + n2)
  | IntExpr.sub e1 e2 => do
    let n1 ← evalIntExpr e1
    let n2 ← evalIntExpr e2
    pure (n1 - n2)
  | IntExpr.mul e1 e2 => do
    let n1 ← evalIntExpr e1
    let n2 ← evalIntExpr e2
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
    let n1 ← evalIntExpr e1
    let n2 ← evalIntExpr e2
    pure (n1 == n2)
  | BoolExpr.neq e1 e2 => do
    let n1 ← evalIntExpr e1
    let n2 ← evalIntExpr e2
    pure (n1 != n2)
  | BoolExpr.lt e1 e2 => do
    let n1 ← evalIntExpr e1
    let n2 ← evalIntExpr e2
    pure (n1 < n2)
  | BoolExpr.leq e1 e2 => do
    let n1 ← evalIntExpr e1
    let n2 ← evalIntExpr e2
    pure (n1 ≤ n2)
  | BoolExpr.gt e1 e2 => do
    let n1 ← evalIntExpr e1
    let n2 ← evalIntExpr e2
    pure (n1 > n2)
  | BoolExpr.geq e1 e2 => do
    let n1 ← evalIntExpr e1
    let n2 ← evalIntExpr e2
    pure (n1 ≥ n2)
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
    let value ← evalIntExpr expr
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
    unless (not condition) do
      runProgram body
      runProgram (IMPProgram.«while» cond body)
decreasing_by all_goals sorry

partial def IMPProgram.runProgramPartial : IMPProgram → IMPComputation Unit
  | IMPProgram.skip => pure ()
  | IMPProgram.assign varName expr => do
    let value ← evalIntExpr expr
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
  IMPProgram.seq (IMPProgram.assign "n" (IntExpr.const 3)) -- n := 3
  (IMPProgram.seq (IMPProgram.assign "result" (IntExpr.const 1)) -- result := 1
    (IMPProgram.«while» (BoolExpr.gt (IntExpr.var "n") (IntExpr.const 0)) -- while n > 0
      (IMPProgram.seq (IMPProgram.assign "result" (IntExpr.mul (IntExpr.var "result") (IntExpr.var "n"))) -- result := result * n
           (IMPProgram.assign "n" (IntExpr.sub (IntExpr.var "n") (IntExpr.const 1))) -- n := n - 1
      )
    )
  )

#eval (factorialProgram.runPartial []).lookup "result"
