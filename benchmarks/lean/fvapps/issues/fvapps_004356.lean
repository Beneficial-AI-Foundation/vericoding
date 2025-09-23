-- <vc-preamble>
def string_binary_to_int (s : String) : Int := sorry
def calculate_to_int (s : String) : Int := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate (n1 n2 : String) (op : Op) : String := sorry

/- Result is a valid binary string (possibly with leading minus) -/
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_binary_valid (n1 n2 : String) (op : Op)
  (h1 : ∀ c ∈ n1.data, c = '0' ∨ c = '1')
  (h2 : ∀ c ∈ n2.data, c = '0' ∨ c = '1') :
  ∀ c ∈ (calculate n1 n2 op).data.filter (· ≠ '-'), c = '0' ∨ c = '1' := sorry

/- Converting strings to ints and evaluating preserves values -/

theorem calculate_preserves_values (n1 n2 : String) (op : Op)
  (h1 : ∀ c ∈ n1.data, c = '0' ∨ c = '1')
  (h2 : ∀ c ∈ n2.data, c = '0' ∨ c = '1') :
  match op with
  | Op.add => calculate_to_int (calculate n1 n2 op) = string_binary_to_int n1 + string_binary_to_int n2
  | Op.subtract => calculate_to_int (calculate n1 n2 op) = string_binary_to_int n1 - string_binary_to_int n2
  | Op.multiply => calculate_to_int (calculate n1 n2 op) = string_binary_to_int n1 * string_binary_to_int n2
  := sorry

/- Invalid inputs raise errors -/

theorem calculate_invalid_input (n1 n2 : String) :
  (∃ c ∈ n1.data, c ≠ '0' ∧ c ≠ '1') → Option.isNone (Option.some (calculate n1 n2 Op.add)) := sorry

/-
info: '10'
-/
-- #guard_msgs in
-- #eval calculate "1" "1" "add"

/-
info: '100'
-/
-- #guard_msgs in
-- #eval calculate "10" "10" "multiply"

/-
info: '10'
-/
-- #guard_msgs in
-- #eval calculate "100" "10" "subtract"
-- </vc-theorems>