-- <vc-preamble>
def find_triangle (h : Int) (s : Int) : Int × Int × Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def format_output (triangle : Int × Int × Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_triangle_valid_output {h s : Int} 
  (h_pos : h > 0) (s_pos : s > 0) (h_bound : h ≤ 1000000) (s_bound : s ≤ 1000000) :
  let (a, b, c) := find_triangle h s
  if a ≠ -1 then
    a > 0 ∧ b > 0 ∧ c > 0 ∧  -- Positive sides
    c = h ∧                   -- Height matches
    a * b / 2 = s ∧          -- Area matches
    a ≤ b                    -- Ordered sides
  else True := sorry

theorem format_output_valid {h s : Int}
  (h_pos : h > 0) (s_pos : s > 0) (h_bound : h ≤ 1000000) (s_bound : s ≤ 1000000) :
  let result := format_output (find_triangle h s)
  if result ≠ "-1" then
    -- Simplified String validation since we lack string manipulation operations
    result.length > 0
  else True := sorry

theorem triangle_inequality {h s : Int}
  (h_pos : h > 0) (s_pos : s > 0) (h_bound : h ≤ 1000) (s_bound : s ≤ 1000) :
  let (a, b, c) := find_triangle h s
  if a ≠ -1 then
    a + b > c ∧ b + c > a ∧ a + c > b  -- Triangle inequality
  else True := sorry

/-
info: '3.000000 4.000000 5.000000'
-/
-- #guard_msgs in
-- #eval format_output find_triangle(5, 6)

/-
info: '-1'
-/
-- #guard_msgs in
-- #eval format_output find_triangle(6, 10)

/-
info: '285168.817674 546189.769984 616153.000000'
-/
-- #guard_msgs in
-- #eval format_output find_triangle(616153, 77878145466)
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded