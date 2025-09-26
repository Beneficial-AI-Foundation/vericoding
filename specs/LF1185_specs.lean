-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_cube_sides {α : Type} [DecidableEq α] (colors : List α) : String := sorry

theorem check_cube_sides_returns_valid_result {α : Type} [DecidableEq α] [Inhabited α]
  (colors : List α) (h : colors.length = 6) :
  check_cube_sides colors = "YES" ∨ check_cube_sides colors = "NO" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_cube_sides_yes_has_adjacent_set {α : Type} [DecidableEq α] [Inhabited α]
  (colors : List α) (h : colors.length = 6) :
  check_cube_sides colors = "YES" →
  ∃ i j k, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ 
          i < colors.length ∧ j < colors.length ∧ k < colors.length ∧
          colors[i]! = colors[j]! ∧ colors[j]! = colors[k]! := sorry

theorem check_cube_sides_no_has_no_adjacent_set {α : Type} [DecidableEq α] [Inhabited α]
  (colors : List α) (h : colors.length = 6) :
  check_cube_sides colors = "NO" →
  ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
          i < colors.length → j < colors.length → k < colors.length →
          ¬(colors[i]! = colors[j]! ∧ colors[j]! = colors[k]!) := sorry

theorem all_same_color_returns_yes {α : Type} [DecidableEq α] [Inhabited α]
  (colors : List α) (h : colors.length = 6)
  (h_same : ∀ i j, i < colors.length → j < colors.length → colors[i]! = colors[j]!) :
  check_cube_sides colors = "YES" := sorry
-- </vc-theorems>