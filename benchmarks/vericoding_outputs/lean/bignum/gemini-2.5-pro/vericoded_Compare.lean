import Mathlib
-- <vc-preamble>

namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
-- </vc-preamble>

-- <vc-helpers>

-- The Compare function is implemented by converting the string representations
-- to Nat values and then comparing those. This approach is straightforward
-- and does not require any helper definitions for this step.

-- </vc-helpers>


-- <vc-definitions>
def Compare (s1 s2 : String) : Int :=
  if Str2Int s1 < Str2Int s2 then -1
  else if Str2Int s1 > Str2Int s2 then 1
  else 0
-- </vc-definitions>

-- <vc-theorems>
theorem Compare_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  (Str2Int s1 < Str2Int s2 → Compare s1 s2 = (-1 : Int)) ∧
  (Str2Int s1 = Str2Int s2 → Compare s1 s2 = 0) ∧
  (Str2Int s1 > Str2Int s2 → Compare s1 s2 = 1) := by
  unfold Compare
  -- We prove each of the three conjuncts separately.
  constructor
  · -- Case 1: Str2Int s1 < Str2Int s2
    intro h_lt
    -- The 'if' condition `Str2Int s1 < Str2Int s2` is true.
    simp [h_lt]
  · constructor
    · -- Case 2: Str2Int s1 = Str2Int s2
      intro h_eq
      -- After substituting with h_eq, both comparisons are false.
      simp [h_eq]
    · -- Case 3: Str2Int s1 > Str2Int s2
      intro h_gt
      -- `simp` needs help to deduce that `Str2Int s1 < Str2Int s2` is false from `h_gt`.
      -- We provide `lt_asymm h_gt`, which is a proof of this fact.
      simp [h_gt, lt_asymm h_gt]
-- </vc-theorems>

end BignumLean
