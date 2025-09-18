-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_happy_string (n k : Nat) : String :=
  sorry

def all_chars_abc (s : String) : Bool :=
  sorry

def no_adjacent_same (s : String) : Bool :=
  sorry

def starts_with_a (s : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem happy_string_properties (n k : Nat)
  (h1 : 0 < n) (h2 : n ≤ 10) (h3 : 0 < k) (h4 : k ≤ 1000) :
  let s := get_happy_string n k
  let max_possible := 3 * 2^(n-1)

  (s.length = n ∨ s.length = 0) ∧

  all_chars_abc s ∧

  (s.length > 1 → no_adjacent_same s) ∧

  ((k > max_possible → s.length = 0) ∧
   (k ≤ max_possible → s.length = n)) :=
sorry

theorem n1_special_case (k : Nat)
  (h1 : 0 < k) (h2 : k ≤ 10) :
  let s := get_happy_string 1 k
  (k ≤ 3 → (s = "a" ∨ s = "b" ∨ s = "c")) ∧
  (k > 3 → s = "") :=
sorry

theorem k1_special_case (n : Nat)
  (h1 : 0 < n) (h2 : n ≤ 5) :
  let s := get_happy_string n 1
  s.length = n ∧
  starts_with_a s :=
sorry
-- </vc-theorems>