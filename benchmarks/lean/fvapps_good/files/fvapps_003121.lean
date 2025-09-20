-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def union_jack (n : α) : String := sorry

theorem size_properties {n : Nat} (h : n ≥ 7) :
  let result := union_jack n
  let lines := result.splitOn "\n"
  (lines.length = max 7 n) ∧ 
  (∀ line ∈ lines, line.length = max 7 n) ∧
  (∀ line ∈ lines, ∀ c ∈ line.data, c = 'X' ∨ c = '-') := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem symmetry_properties {n : Nat} (h : n = 7 ∨ n = 8) :
  let result := union_jack n
  let lines := result.splitOn "\n"
  (∀ i < lines.length,
    lines[i]! = String.mk (List.reverse lines[i]!.data) ∧ 
    lines[i]! = lines[lines.length - 1 - i]!) := sorry
-- </vc-theorems>