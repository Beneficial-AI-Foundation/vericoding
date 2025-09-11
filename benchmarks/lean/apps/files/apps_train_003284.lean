-- <vc-preamble>
def factorial : Nat → Nat
  | 0 => 1 
  | n + 1 => (n + 1) * factorial n

def List.prod : List Nat → Nat
  | [] => 1
  | x :: xs => x * prod xs

def isAscii (s : String) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def uniq_count (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem uniq_count_positive (s : String) :
  uniq_count s > 0 :=
  sorry

theorem uniq_count_empty :
  uniq_count "" = 1 :=
  sorry

theorem uniq_count_factorial_bound (s : String) :
  uniq_count s ≤ factorial s.length :=
  sorry

theorem uniq_count_unique_chars {s : String} (h₁ : s ≠ "") 
  (h₂ : (s.toLower.data.eraseDups).length = s.length) :
  uniq_count s = factorial s.length :=
  sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval uniq_count "ABC"

/-
info: 3
-/
-- #guard_msgs in
-- #eval uniq_count "ABA"

/-
info: 24
-/
-- #guard_msgs in
-- #eval uniq_count "AbcD"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible