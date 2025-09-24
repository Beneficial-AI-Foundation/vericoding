-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def billboard (name : String) (price : Nat := 30) : Nat := sorry

theorem billboard_properties {name : String} {price : Nat} 
  (h1 : name.length > 0) (h2 : price > 0) (h3 : price ≤ 1000) :
  let result := billboard name price
  (result = name.length * price) ∧ 
  (result ≥ price) ∧
  (result % price = 0) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem billboard_default_price {name : String} (h : name.length > 0) : 
  let result := billboard name
  (result = name.length * 30) ∧ 
  (result % 30 = 0) := sorry

theorem billboard_general {name : String} :
  let result := billboard name
  (result ≥ 0) ∧
  (name.length * 30 = result) := sorry
-- </vc-theorems>