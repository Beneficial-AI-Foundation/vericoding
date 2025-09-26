import Mathlib
-- <vc-preamble>

namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def intOfCmp (a b : Nat) : Int :=
  if a < b then (-1 : Int) else if a = b then 0 else 1

-- LLM HELPER
 theorem intOfCmp_spec (a b : Nat) :
  (a < b → intOfCmp a b = (-1 : Int)) ∧
  (a = b → intOfCmp a b = 0) ∧
  (a > b → intOfCmp a b = 1) := by
  unfold intOfCmp
  constructor
  · intro hlt
    simp [hlt]
  · constructor
    · intro heq
      simp [heq]
    · intro hgt
      have hnotlt : ¬ a < b := not_lt_of_ge (le_of_lt hgt)
      have hneq : a ≠ b := ne_of_gt hgt
      simp [hnotlt, hneq]

-- </vc-helpers>


-- <vc-definitions>
def Compare (s1 s2 : String) : Int :=
  intOfCmp (Str2Int s1) (Str2Int s2)
-- </vc-definitions>

-- <vc-theorems>
theorem Compare_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  (Str2Int s1 < Str2Int s2 → Compare s1 s2 = (-1 : Int)) ∧
  (Str2Int s1 = Str2Int s2 → Compare s1 s2 = 0) ∧
  (Str2Int s1 > Str2Int s2 → Compare s1 s2 = 1) := by
  unfold Compare
  exact intOfCmp_spec (Str2Int s1) (Str2Int s2)
-- </vc-theorems>

end BignumLean
