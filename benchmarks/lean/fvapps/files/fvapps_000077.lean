-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Grid := List (List Char)

def min_minutes_for_cross (grid : Grid) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_minutes_bounds {grid : Grid} :
  let n := grid.length
  let m := grid.head!.length
  0 ≤ min_minutes_for_cross grid ∧ min_minutes_for_cross grid ≤ n + m - 1 :=
sorry

theorem center_cross_pattern {grid : Grid} (h : grid.length ≥ 3) :
  let n := grid.length
  let m := grid.head!.length
  let mid_row := n / 2
  let mid_col := m / 2
  let cross_grid := List.map (fun i => 
    List.map (fun j => 
      if i = mid_row ∨ j = mid_col then '*' else '.'
    ) (List.range m)
  ) (List.range n)
  min_minutes_for_cross cross_grid = 0 :=
sorry

theorem all_asterisks_returns_zero {grid : Grid} :
  let n := grid.length
  let m := grid.head!.length
  let all_asterisk_grid := List.map (fun _ => 
    List.map (fun _ => '*') (List.range m)
  ) (List.range n)
  min_minutes_for_cross all_asterisk_grid = 0 :=
sorry

theorem all_dots_minutes {grid : Grid} :
  let n := grid.length
  let m := grid.head!.length
  let all_dots_grid := List.map (fun _ => 
    List.map (fun _ => '.') (List.range m)
  ) (List.range n)
  min_minutes_for_cross all_dots_grid = n + m - 1 :=
sorry
-- </vc-theorems>