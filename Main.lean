import LeanIMP
import LeanIMP.BigStep
import LeanIMP.Equivalence

unsafe def main : IO Unit :=
  let ⟨result, proof⟩ := (runBigStep (whileLoopProgram2 10) [])
  IO.println s!"Successfully ran program! Result x: {result.head!.snd}"
