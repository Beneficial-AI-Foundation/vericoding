-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_divisible_by_6 (s: String): List String := sorry

def verify_divisible_by_6 (s: String): Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_number_without_wildcards (n: Nat) :
  let s := toString n
  n % 6 = 0 → is_divisible_by_6 s = [s] ∧
  n % 6 ≠ 0 → is_divisible_by_6 s = [] :=
sorry  

theorem wildcard_pattern_properties (n: Nat) (h: 1 ≤ n ∧ n ≤ 5) :
  let pattern := String.mk (List.replicate n '*')
  ∀ num ∈ is_divisible_by_6 pattern,
    String.length num = n ∧
    verify_divisible_by_6 num = true ∧ 
    ∀ c ∈ String.toList num, '0' ≤ c ∧ c ≤ '9' :=
sorry

theorem odd_ending_gives_empty {d: Char} (h: d ∈ ['1', '3', '5', '7', '9']) : 
  is_divisible_by_6 ("*" ++ toString d) = [] :=
sorry

/-
info: ['12', '42', '72']
-/
-- #guard_msgs in
-- #eval is_divisible_by_6 "*2"

/-
info: []
-/
-- #guard_msgs in
-- #eval is_divisible_by_6 "*21"

/-
info: ['024', '120', '126', '222', '228', '324', '420', '426', '522', '528', '624', '720', '726', '822', '828', '924']
-/
-- #guard_msgs in
-- #eval is_divisible_by_6 "*2*"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded