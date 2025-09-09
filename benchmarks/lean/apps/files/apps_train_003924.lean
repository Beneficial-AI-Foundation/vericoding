def is_square (n : Int) : Bool :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def Int.sqrt (n : Int) : Int :=
sorry

theorem is_square_properties_1 {n : Int} : 
  is_square n = true → n ≥ 0 :=
sorry

theorem is_square_properties_3 {n : Nat} :
  is_square (n * n) = true :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible