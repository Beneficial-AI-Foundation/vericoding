-- <vc-helpers>
-- </vc-helpers>

def CombString := String -- represents strings of only * and .

def combs (a b : CombString) : Nat := sorry

/- The result length is at least as long as the longest input -/

theorem combs_min_length {a b : CombString} :
  combs a b ≥ max a.length b.length := sorry

/- The result length is at most the sum of input lengths -/

theorem combs_max_length {a b : CombString} :
  combs a b ≤ a.length + b.length := sorry

/- The function is symmetric -/

theorem combs_symmetric {a b : CombString} :
  combs a b = combs b a := sorry

/- Strings of all dots combine to max length -/

theorem combs_all_dots {a b : CombString}
  (ha : ∀ c, c ∈ a.data → c = '.')
  (hb : ∀ c, c ∈ b.data → c = '.') :
  combs a b = max a.length b.length := sorry

/- Strings of all stars combine to sum of lengths -/

theorem combs_all_stars {a b : CombString}
  (ha : ∀ c, c ∈ a.data → c = '*')
  (hb : ∀ c, c ∈ b.data → c = '*') :
  combs a b = a.length + b.length := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval combs "*..*" "*.*"

/-
info: 5
-/
-- #guard_msgs in
-- #eval combs "*...*" "*.*"

/-
info: 9
-/
-- #guard_msgs in
-- #eval combs "*..*.*" "*.***"

-- Apps difficulty: introductory
-- Assurance level: guarded