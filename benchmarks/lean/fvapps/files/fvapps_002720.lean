-- <vc-preamble>
def CombString := String
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def combs (a b : CombString) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem combs_min_length {a b : CombString} :
  combs a b ≥ max a.length b.length :=
sorry

theorem combs_max_length {a b : CombString} :
  combs a b ≤ a.length + b.length :=
sorry

theorem combs_symmetric {a b : CombString} :
  combs a b = combs b a :=
sorry

theorem combs_all_dots {a b : CombString}
  (ha : ∀ c, c ∈ a.data → c = '.')
  (hb : ∀ c, c ∈ b.data → c = '.') :
  combs a b = max a.length b.length :=
sorry

theorem combs_all_stars {a b : CombString}
  (ha : ∀ c, c ∈ a.data → c = '*')
  (hb : ∀ c, c ∈ b.data → c = '*') :
  combs a b = a.length + b.length :=
sorry
-- </vc-theorems>