
abbrev IMPState (α: Type) [BEq α] : Type := (List (α × Nat))

instance (α: Type) [BEq α] : Inhabited (IMPState α) where
  default := []

def IMPState.update {α: Type} [BEq α] (s: IMPState α) (key: α) (value: Nat) :=
  (key, value) :: s

def IMPState.prepend_updates {α: Type} [BEq α] (s1 s2: IMPState α) :=
  List.foldr (fun (k, v) l  => IMPState.update l (k:α) v) s1 s2


def IMPState.does_not_contain {α: Type} [BEq α] (s: IMPState α) (k: α) : Prop :=
  match s with
  | List.nil => True
  | (a, _)::as => And (¬ (a == k)) (IMPState.does_not_contain as k)

abbrev IMPComputation (α β : Type) [BEq α] : Type := StateM (IMPState α) β

def addPair {α: Type} [BEq α] (key: α) (value: Nat) : (IMPComputation α) Unit := do
  let s ← get
  set (s.update key value)


inductive NatExpr (α: Type) [BEq α] where
  | var (_:α)
  | const (_:Nat)
  | add (_ _: NatExpr α)
  | sub (_ _: NatExpr α)
  | mul (_ _: NatExpr α)

def NatExpr.does_not_contain {α: Type} [BEq α] (expr: NatExpr α) (s: α) : Prop :=
  match expr with
    | var (v:α) => ¬(v = s)
    | const (_:Nat) => True
    | add (x : NatExpr α) (y: NatExpr α) => And (x.does_not_contain s) (y.does_not_contain s)
    | sub (x : NatExpr α) (y: NatExpr α) => And (x.does_not_contain s) (y.does_not_contain s)
    | mul (x : NatExpr α) (y: NatExpr α) => And (x.does_not_contain s) (y.does_not_contain s)


inductive BoolExpr (α: Type) [BEq α] where
  | var (_:α)
  | const (_:Bool)
  | eq (_ _: NatExpr α)
  | neq (_ _: NatExpr α)
  | lt (_ _: NatExpr α)
  | leq (_ _: NatExpr α)
  | gt (_ _: NatExpr α)
  | geq (_ _: NatExpr α)
  | or (_ _: BoolExpr α)
  | and (_ _: BoolExpr α)
  | not (_: BoolExpr α)

def BoolExpr.does_not_contain {α: Type} [BEq α] (expr: BoolExpr α) (s: α) : Prop :=
  match expr with
    | var (v) => ¬(v = s)
    | const (_:Bool) => True
    | eq (x : NatExpr α) (y : NatExpr α) => And (x.does_not_contain s) (y.does_not_contain s)
    | neq (x : NatExpr α) (y: NatExpr α) => And (x.does_not_contain s) (y.does_not_contain s)
    | lt (x : NatExpr α) (y: NatExpr α) => And (x.does_not_contain s) (y.does_not_contain s)
    | leq (x : NatExpr α) (y: NatExpr α) => And (x.does_not_contain s) (y.does_not_contain s)
    | gt (x : NatExpr α) (y: NatExpr α ) => And (x.does_not_contain s) (y.does_not_contain s)
    | geq (x : NatExpr α) (y: NatExpr α) => And (x.does_not_contain s) (y.does_not_contain s)
    | or (x : BoolExpr α) (y: BoolExpr α) => And (x.does_not_contain s) (y.does_not_contain s)
    | and (x : BoolExpr α) (y: BoolExpr α) => And (x.does_not_contain s) (y.does_not_contain s)
    | not (x : BoolExpr α) => x.does_not_contain s


inductive IMPProgram (α: Type) [BEq α] where
  | skip
  | assign (var: α) (expr: NatExpr α)
  | seq (_ _: IMPProgram α)
  | «if» (_: BoolExpr α) (_ _: IMPProgram α)
  | «while» (_: BoolExpr α) (_: IMPProgram α)


def evalNatExpr {α: Type} [BEq α] : NatExpr α → IMPComputation α Nat
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

def evalBoolExpr {α: Type} [BEq α] : BoolExpr α → IMPComputation α Bool
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

partial def IMPProgram.runProgramPartial {α: Type} [BEq α] : (IMPProgram α) → IMPComputation α Unit
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


def IMPProgram.runPartial {α: Type} [BEq α] (program: IMPProgram α) (state: IMPState α) :=
  let (_, state) := (runProgramPartial program).run state |>.run
  state
