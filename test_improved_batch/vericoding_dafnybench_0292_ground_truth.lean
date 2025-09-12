/-
  Port of vericoding_dafnybench_0292_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def numRescueBoats (people : number[]) (limit : number) : number :=
  sorry  -- TODO: implement function body

function binsort(nums: number[], limit: number) {
  sorry  -- TODO: implement function body

def sumBoat (s : seq<nat>) : Nat :=
  sorry  -- TODO: implement complex function body

def multisetAdd (ss : seq<seq<nat>>) : multiset :=
  sorry  -- TODO: implement function body

def numRescueBoats (people : seq<nat>) (limit : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem numRescueBoats_spec (people : seq<nat>) (limit : Nat) (boats : Nat) :=
  (h_0 : |people| ≥ 1)
  (h_1 : sorted(people))
  (h_2 : ∀ i : nat, i < |people| → 1 ≤ people[i]! ≤ limit)
  : ∃ boatConfig: seq<seq<nat>> :: multisetEqual(boatConfig, people) ∧ allSafe(boatConfig, limit) ∧ boats == |boatConfig|// ∧ ∀ boatConfigs :: multisetEqual(boatConfigs, people) ∧ allSafe(boatConfigs, limit) → boats ≤ |boatConfigs|
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks