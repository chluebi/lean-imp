import LeanIMP.Basic

inductive IMPSmallStepState (α: Type) [BEq α] where
  | ss_unfinished : IMPProgram α → IMPState α → IMPSmallStepState α
  | ss_finished : IMPState α → IMPSmallStepState α

inductive SmallStep {α: Type} [BEq α] : IMPProgram α → IMPState α → IMPSmallStepState α → Prop where
  | ss_skip (s : IMPState α) :
    SmallStep IMPProgram.skip s (IMPSmallStepState.ss_finished s)
  | ss_assign (x : α) (e : NatExpr α) (s : IMPState α) (val : Nat) :
    (evalNatExpr e).run s = (val, s) ->
    SmallStep (IMPProgram.assign x e) s (IMPSmallStepState.ss_finished (s.update x val))
  | ss_seq1 (p1 p2 : IMPProgram α) (s s' : IMPState α) :
    SmallStep p1 s (IMPSmallStepState.ss_finished s') ->
    SmallStep (IMPProgram.seq p1 p2) s (IMPSmallStepState.ss_unfinished p2 s')
  | ss_seq2 (p1 p2 p3 : IMPProgram α) (s s' : IMPState α) :
    SmallStep p1 s (IMPSmallStepState.ss_unfinished p3 s') ->
    SmallStep (IMPProgram.seq p1 p2) s (IMPSmallStepState.ss_unfinished (IMPProgram.seq p3 p2) s')
  | ss_if_true (b_expr : BoolExpr α) (p_then p_else : IMPProgram α) (s : IMPState α) :
    (evalBoolExpr b_expr).run s = (true, s) ->
    SmallStep (IMPProgram.«if» b_expr p_then p_else) s (IMPSmallStepState.ss_unfinished p_then s)
  | ss_if_false (b_expr : BoolExpr α) (p_then p_else : IMPProgram α) (s : IMPState α) :
    (evalBoolExpr b_expr).run s = (false, s) ->
    SmallStep (IMPProgram.«if» b_expr p_then p_else) s (IMPSmallStepState.ss_unfinished p_else s)
  | ss_while (b_expr : BoolExpr α) (p_body : IMPProgram α) (s : IMPState α) :
    SmallStep (IMPProgram.«while» b_expr p_body) s (
      IMPSmallStepState.ss_unfinished (
        (IMPProgram.«if» b_expr (
          IMPProgram.seq (p_body) (IMPProgram.«while» b_expr p_body)
        ) IMPProgram.skip)
      )
      s
    )

notation "⟨" p:1 "," s:0 "⟩" " ->1 " s':0 => SmallStep p s (IMPSmallStepState.ss_finished s')
notation "⟨" p:1 "," s:0 "⟩" " ->1 " "⟨" p':1 "," s':0 "⟩" => SmallStep p s (IMPSmallStepState.ss_unfinished p' s')

inductive SmallStepSequence {α: Type} [BEq α] : IMPProgram α → IMPState α → IMPState α → Nat -> Prop where
  | single (p: IMPProgram α) (s s': IMPState α) :
    SmallStep p s (IMPSmallStepState.ss_finished s') ->
    SmallStepSequence p s s' 1
  | cons (p1 p2: IMPProgram α) (s s' s'': IMPState α) (k: Nat) :
    SmallStep p1 s (IMPSmallStepState.ss_unfinished p2 s') ->
    SmallStepSequence p2 s' s'' k ->
    SmallStepSequence p1 s s'' (1 + k)

notation "⟨" p:1 "," s:0 "⟩" " ->*" " [" n "] " s':0 => SmallStepSequence p s s' n
