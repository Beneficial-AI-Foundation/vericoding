-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_triangle (h : Int) (s : Int) : Int × Int × Int :=
  sorry

def format_output (triangle : Int × Int × Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_triangle_valid_output {h s : Int}
  (h_pos : h > 0) (s_pos : s > 0) (h_bound : h ≤ 1000000) (s_bound : s ≤ 1000000) :
  let (a, b, c) := find_triangle h s
  if a ≠ -1 then
    a > 0 ∧ b > 0 ∧ c > 0 ∧
    c = h ∧
    a * b / 2 = s ∧
    a ≤ b
  else True :=
sorry

theorem format_output_valid {h s : Int}
  (h_pos : h > 0) (s_pos : s > 0) (h_bound : h ≤ 1000000) (s_bound : s ≤ 1000000) :
  let result := format_output (find_triangle h s)
  if result ≠ "-1" then

    result.length > 0
  else True :=
sorry

theorem triangle_inequality {h s : Int}
  (h_pos : h > 0) (s_pos : s > 0) (h_bound : h ≤ 1000) (s_bound : s ≤ 1000) :
  let (a, b, c) := find_triangle h s
  if a ≠ -1 then
    a + b > c ∧ b + c > a ∧ a + c > b
  else True :=
sorry
-- </vc-theorems>