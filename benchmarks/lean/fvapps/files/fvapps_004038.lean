-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mark_spot (input : α) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mark_spot_invalid_types {α : Type} (x : α) : 
  mark_spot x = "?" :=
sorry

theorem mark_spot_odd_numbers {n : Nat} (h1 : n ≥ 1) (h2 : n ≤ 99) (h3 : n % 2 = 1) :
  let result := mark_spot n
  -- Result is not "?"
  result ≠ "?" ∧ 
  -- Can split into n lines 
  (let lines := (result.trim.splitOn "\n")
   lines.length = n ∧
  -- Each line contains X
   (∀ line ∈ lines, line.contains 'X') ∧
  -- All lines except middle have 2 Xs
   (∀ i < lines.length, 
      if i = n / 2 
      then ∃ j : Fin (lines.get! i).length, (lines.get! i).data.get j = 'X'
      else ∃ j k : Fin (lines.get! i).length, j ≠ k ∧
           (lines.get! i).data.get j = 'X' ∧ 
           (lines.get! i).data.get k = 'X')) :=
sorry
-- </vc-theorems>