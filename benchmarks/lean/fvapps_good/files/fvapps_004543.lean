-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def two_sum (numbers : List Int) (target : Int) : Option (Nat × Nat) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem two_sum_correct_sum 
  (numbers : List Int) 
  (target : Int)
  (h : numbers.length ≥ 2)
  (result : Option (Nat × Nat))
  (hresult : result = two_sum numbers target) :
  result.map (fun (ij : Nat × Nat) => 
    numbers.get! ij.fst + numbers.get! ij.snd = target) = some true :=
sorry

theorem two_sum_exists_for_sum_of_elements
  (numbers : List Int)
  (h : numbers.length ≥ 2) :
  let target := numbers.get! 0 + numbers.get! 1
  let result := two_sum numbers target
  result.isSome ∧ 
  result.map (fun ij => numbers.get! ij.fst + numbers.get! ij.snd = target) = some true :=
sorry

theorem two_sum_different_indices
  (numbers : List Int)
  (h : numbers.length ≥ 2) :
  let target := numbers.get! 0 + numbers.get! 1
  let result := two_sum numbers target
  result.map (fun ij => ij.fst ≠ ij.snd) = some true :=
sorry
-- </vc-theorems>