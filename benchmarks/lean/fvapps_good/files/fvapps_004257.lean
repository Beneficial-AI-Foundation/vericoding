-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : String) : String := sorry

theorem solve_contains_non_common_chars (a b : String) (c : Char) :
  c ∈ a.data ∨ c ∈ b.data →
  (¬ (c ∈ a.data ∧ c ∈ b.data)) →
  c ∈ (solve a b).data
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_excludes_common_chars (a b : String) :
  ∀ c, c ∈ (solve a b).data →
  ¬ (c ∈ a.data ∧ c ∈ b.data)
  := sorry

theorem solve_maintains_relative_order (a b : String) :
  let a_filtered := a.data.filter (fun c => ¬(c ∈ a.data ∧ c ∈ b.data))
  let b_filtered := b.data.filter (fun c => ¬(c ∈ a.data ∧ c ∈ b.data))
  solve a b = String.mk (a_filtered ++ b_filtered)
  := sorry

theorem solve_length_property (a b : String) :
  let a_filtered := a.data.filter (fun c => ¬(c ∈ a.data ∧ c ∈ b.data))
  let b_filtered := b.data.filter (fun c => ¬(c ∈ a.data ∧ c ∈ b.data))
  (solve a b).length = a_filtered.length + b_filtered.length
  := sorry

theorem solve_identical_strings (s : String) :
  solve s s = ""
  := sorry

theorem solve_with_empty (s : String) :
  solve s "" = s ∧
  solve "" s = s
  := sorry
-- </vc-theorems>