-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chameleon (chameleons : List Nat) (color : Nat) : Int := sorry

theorem chameleon_result_is_valid 
  (chameleons : List Nat) 
  (color : Nat)
  (h1 : chameleons.length = 3)
  (h2 : color ≤ 2) :
  let result := chameleon chameleons color
  (result = -1 ∨ result ≥ 0) ∧
  (result = -1 ∨ 
    ∃ a b c : Nat,
      (a > 0 ∨ c > 0) ∧ 
      (b - a) % 3 = 0 ∧ 
      result = b)
  := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>