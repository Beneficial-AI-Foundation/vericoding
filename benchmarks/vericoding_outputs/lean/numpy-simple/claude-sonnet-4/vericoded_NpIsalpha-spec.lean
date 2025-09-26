import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Helper function to check if a string is alphabetic
def String.isAlphaOnly (s : String) : Bool :=
  s.length > 0 ∧ s.all Char.isAlpha
-- </vc-helpers>

-- <vc-definitions>
def isAlpha {n : Nat} (input : Vector String n) : Vector Bool n :=
Vector.map (fun s => s.length > 0 ∧ s.all fun c => ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z')) input
-- </vc-definitions>

-- <vc-theorems>
theorem isAlpha_spec {n : Nat} (input : Vector String n) :
  let ret := isAlpha input
  (ret.toList.length = n) ∧
  (∀ i : Fin n, ret[i] = (input[i].length > 0 ∧
    input[i].all fun c => ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z'))) :=
by
  constructor
  · -- Prove length equality
    simp [isAlpha, Vector.toList_map, List.length_map]
  · -- Prove correctness of each element
    intro i
    simp [isAlpha, Vector.get_map]
-- </vc-theorems>
