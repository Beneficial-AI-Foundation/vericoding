-- <vc-helpers>
-- </vc-helpers>

def solve_fruit_basket (a b c d : Int) : Int × Int × Int := sorry

theorem fruit_basket_solution_properties {a b c d : Int}
  (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (h_valid : ∃ (apples mangoes oranges : Int),
    apples + mangoes == a ∧
    mangoes + oranges == b ∧ 
    oranges + apples == c ∧
    apples + mangoes + oranges == d) : 
  let (apples, mangoes, oranges) := solve_fruit_basket a b c d
  0 ≤ apples ∧ 0 ≤ mangoes ∧ 0 ≤ oranges ∧
  apples + mangoes == a ∧
  mangoes + oranges == b ∧
  oranges + apples == c ∧
  apples + mangoes + oranges == d := sorry

theorem fruit_basket_returns_ints {a b c d : Int} :
  let (x, y, z) := solve_fruit_basket a b c d
  ∃ (r s t : Int), x = r ∧ y = s ∧ z = t := sorry

-- Apps difficulty: interview
-- Assurance level: guarded