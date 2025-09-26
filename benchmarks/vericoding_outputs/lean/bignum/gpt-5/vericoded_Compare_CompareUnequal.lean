import Mathlib
-- <vc-preamble>

namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0


def CompareUnequal (s1 s2 : String) : Int :=
  sorry

axiom CompareUnequal_spec
    (s1 s2 : String)
    (h1 : ValidBitString s1)
    (h2 : ValidBitString s2)
    (h10 : s1.length > 0)
    (h1nz : s1.length > 1 → s1.get? 0 = some '1')
    (h20 : s2.length > 0)
    (h2nz : s2.length > 1 → s2.get? 0 = some '1')
    (hlen : s1.length > s2.length)
    :
    (Str2Int s1 < Str2Int s2 → CompareUnequal s1 s2 = (-1 : Int)) ∧
    (Str2Int s1 = Str2Int s2 → CompareUnequal s1 s2 = 0) ∧
    (Str2Int s1 > Str2Int s2 → CompareUnequal s1 s2 = 1)


-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem tri_nat_spec (a b : Nat) :
  (a < b → (if a < b then (-1 : Int) else if a = b then 0 else 1) = (-1 : Int)) ∧
  (a = b → (if a < b then (-1 : Int) else if a = b then 0 else 1) = 0) ∧
  (a > b → (if a < b then (-1 : Int) else if a = b then 0 else 1) = 1) := by
  constructor
  · intro hlt; simp [hlt]
  · constructor
    · intro heq; simp [heq]
    · intro hgt
      have hge : a ≥ b := le_of_lt hgt
      have hnotlt : ¬ a < b := not_lt_of_ge hge
      have hneq : a ≠ b := ne_of_gt hgt
      simp [hnotlt, hneq]
-- </vc-helpers>


-- <vc-definitions>
def Compare (s1 s2 : String) : Int :=
  if Str2Int s1 < Str2Int s2 then (-1 : Int) else if Str2Int s1 = Str2Int s2 then 0 else 1
-- </vc-definitions>

-- <vc-theorems>
theorem Compare_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  (Str2Int s1 < Str2Int s2 → Compare s1 s2 = (-1 : Int)) ∧
  (Str2Int s1 = Str2Int s2 → Compare s1 s2 = 0) ∧
  (Str2Int s1 > Str2Int s2 → Compare s1 s2 = 1) := by
  simpa [Compare] using (tri_nat_spec (Str2Int s1) (Str2Int s2))
-- </vc-theorems>

