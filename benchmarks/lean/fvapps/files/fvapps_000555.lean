-- <vc-preamble>
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def containsChar (s : String) (c : Char) : Bool :=
  s.data.contains c
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_distinct_sequences (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_distinct_basic_properties (s : String) :
  let result := count_distinct_sequences s
  result ≤ factorial s.length ∧
  0 < result ∧
  result = result
  :=
sorry

theorem count_distinct_special_substring (s : String) :
  let result := count_distinct_sequences s
  ((containsChar s 'k' ∧ containsChar s 'a' ∧ containsChar s 'r') ∨
   (containsChar s 's' ∧ containsChar s 'h' ∧ containsChar s 'i')) →
  result < factorial s.length
  :=
sorry

theorem count_distinct_karshi_all_letters (s : String) :
  let result := count_distinct_sequences s
  (containsChar s 'k' ∧ containsChar s 'a' ∧ containsChar s 'r' ∧
   containsChar s 's' ∧ containsChar s 'h' ∧ containsChar s 'i') →
  result < factorial s.length - factorial (s.length - 2)
  :=
sorry

theorem count_distinct_exact_karshi (s : String) :
  s.length = 6 →
  (s.data.toArray.qsort (· < ·) = "karshi".data.toArray.qsort (· < ·)) →
  count_distinct_sequences s = factorial 6 - 2 * factorial 4
  :=
sorry

theorem count_distinct_length_properties (s : String) :
  let result := count_distinct_sequences s
  (s.length ≤ 2 → result = factorial s.length) ∧
  (s.length > 6 ∧ containsChar s 'k' ∧ containsChar s 'a' ∧
   containsChar s 'r' ∧ containsChar s 's' ∧ containsChar s 'h' ∧
   containsChar s 'i' →
    result = factorial s.length - 2 * factorial (s.length - 2) + factorial (s.length - 4))
  :=
sorry
-- </vc-theorems>