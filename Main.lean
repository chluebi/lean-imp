import LeanIMP
import LeanIMP.BigStep
import LeanIMP.Equivalence

unsafe def main : IO Unit :=
  let x := (runBigStep (whileLoopProgram2 10) []).snd
  IO.println s!"Hello, world!"
