/-
  Port of fv2020-tms_tmp_tmpnp85b47l_simple_tm_Step.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Step (input : TMSystem) (pid : ProcessId) : TMSystem :=
  sorry  -- TODO: implement function body

theorem Step_spec (input : TMSystem) (pid : ProcessId) (system : TMSystem) :=
  (h_0 : pid in input.txQueues)
  (h_1 : pid in input.procStates)
  (h_2 : input.validSystem())
  : system.validSystem()
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks