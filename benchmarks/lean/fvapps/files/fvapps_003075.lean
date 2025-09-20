-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def my_crib (n : Nat) : String :=
  sorry

def splitLines (s : String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem crib_width_consistency {n : Nat} (h : 1 ≤ n ∧ n ≤ 10) :
  let width := 4 + 3 + 6 * (n - 1)
  let lines := splitLines (my_crib n)
  ∀ line ∈ lines, line.length = width :=
sorry

theorem crib_roof_top {n : Nat} (h : 1 ≤ n ∧ n ≤ 10) :
  let lines := splitLines (my_crib n)
  let first_line := lines.head?
  ∀ line, first_line = some line → line.replace " " "" = line.replace "_" "" :=
sorry

theorem crib_sloping_roof {n : Nat} (h : 1 ≤ n ∧ n ≤ 10) :
  let lines := splitLines (my_crib n)
  let roof_lines := lines.take (3 + 2*(n-1))
  ∀ line ∈ roof_lines, (line.contains '/') ∧ (line.contains '\\') :=
sorry

theorem crib_wall_structure {n : Nat} (h : 1 ≤ n ∧ n ≤ 10) :
  let lines := splitLines (my_crib n)
  let wall_lines := lines.drop (3 + 2*(n-1))
  ∀ line ∈ wall_lines, line.startsWith "|" ∧ line.endsWith "|" :=
sorry

theorem crib_bottom_line {n : Nat} (h : 1 ≤ n ∧ n ≤ 10) :
  let lines := splitLines (my_crib n)
  ∀ last_line, lines.getLast? = some last_line → last_line.contains '_' :=
sorry
-- </vc-theorems>