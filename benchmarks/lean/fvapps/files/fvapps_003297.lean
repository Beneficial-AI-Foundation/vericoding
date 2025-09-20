-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def doubles (s : String) : String := sorry

theorem doubles_idempotent (s : String) :
  doubles (doubles s) = doubles s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem doubles_pairwise (s : String) :
  let result := doubles s
  ∀ i : Nat, i + 1 < result.length → 
  result.data[i]? ≠ result.data[i + 1]? := sorry

theorem doubles_single_char (s : String) :
  s.length ≤ 1 →
  doubles s = s := sorry

theorem doubles_pair (s : String) (h : s.length = 2) :
  (s.data[0]? = s.data[1]? → doubles s = "") ∧
  (s.data[0]? ≠ s.data[1]? → doubles s = s) := sorry

theorem doubles_length_parity (s : String) :
  (s.length - (doubles s).length) % 2 = 0 := sorry
-- </vc-theorems>