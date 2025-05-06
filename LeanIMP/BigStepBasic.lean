import LeanIMP.Basic

inductive BigStep : IMPProgram → IMPState → IMPState → Prop where
  | bs_skip (s : IMPState) :
    BigStep IMPProgram.skip s s
  | bs_assign (x : String) (e : NatExpr) (s : IMPState) (val : Nat) :
    (evalNatExpr e).run s = (val, s) ->
    BigStep (IMPProgram.assign x e) s (s.update x val)
  | bs_seq (p1 p2 : IMPProgram) (s s1 s2 : IMPState) :
    BigStep p1 s s1 ->
    BigStep p2 s1 s2 ->
    BigStep (IMPProgram.seq p1 p2) s s2
  | bs_if_true (b_expr : BoolExpr) (p_then p_else : IMPProgram) (s s' : IMPState) :
    (evalBoolExpr b_expr).run s = (true, s) ->
    BigStep p_then s s' ->
    BigStep (IMPProgram.«if» b_expr p_then p_else) s s'
  | bs_if_false (b_expr : BoolExpr) (p_then p_else : IMPProgram) (s s' : IMPState) :
    (evalBoolExpr b_expr).run s = (false, s) ->
    BigStep p_else s s' ->
    BigStep (IMPProgram.«if» b_expr p_then p_else) s s'
  | bs_while_true (b_expr : BoolExpr) (p_body : IMPProgram) (s s1 s2 : IMPState) :
    (evalBoolExpr b_expr).run s = (true, s) ->
    BigStep p_body s s1 ->
    BigStep (IMPProgram.«while» b_expr p_body) s1 s2 ->
    BigStep (IMPProgram.«while» b_expr p_body) s s2
  | bs_while_false (b_expr : BoolExpr) (p_body : IMPProgram) (s : IMPState) :
    (evalBoolExpr b_expr).run s = (false, s) ->
    BigStep (IMPProgram.«while» b_expr p_body) s s
