-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def print_number (number : Nat) (char : Char) : String := sorry

theorem print_number_dimensions (n : Nat) (c : Char) :
  let result := print_number n c
  let lines := result.splitOn "\n"
  lines.length = 10 ∧ 
  lines.all (fun line => line.length = 40) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem print_number_borders (n : Nat) (c : Char) :
  let result := print_number n c
  let lines := result.splitOn "\n"
  lines.length > 0 ∧ 
  (∀ ch ∈ lines[0]!.data, ch = c) ∧ 
  (∀ ch ∈ lines[lines.length - 1]!.data, ch = c) ∧ 
  lines[1]! = (String.mk [c] ++ String.mk (List.replicate 38 ' ') ++ String.mk [c]) ∧
  lines[lines.length - 2]! = (String.mk [c] ++ String.mk (List.replicate 38 ' ') ++ String.mk [c]) := sorry

theorem print_number_middle_structure (n : Nat) (c : Char) :
  let result := print_number n c
  let lines := result.splitOn "\n"
  ∀ i, 2 ≤ i → i < 8 →
    let line := lines[i]!
    line.get? ⟨0⟩ = some c ∧
    line.get? ⟨line.length - 1⟩ = some c ∧
    (line.take 3).drop 1 = "  " ∧
    (line.take line.length).drop (line.length - 3) = "  " := sorry

theorem print_number_char_independence (n : Nat) :
  (print_number n '*').replace (String.mk ['*']) "#" = print_number n '#' := sorry
-- </vc-theorems>