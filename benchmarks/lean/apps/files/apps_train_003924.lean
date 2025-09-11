-- <vc-preamble>
def is_square (n : Int) : Bool :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Int.sqrt (n : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_square_properties_1 {n : Int} : 
  is_square n = true → n ≥ 0 :=
sorry

theorem is_square_properties_3 {n : Nat} :
  is_square (n * n) = true :=
sorry
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible