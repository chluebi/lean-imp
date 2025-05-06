import LeanIMP.Basic
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
