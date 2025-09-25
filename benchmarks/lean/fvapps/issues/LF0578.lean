-- <vc-preamble>
def List.sum (l : List Int) : Int := 
  match l with
  | [] => 0
  | x :: xs => x + List.sum xs

def List.sumFloat (l : List Float) : Float :=
  match l with
  | [] => 0
  | x :: xs => x + List.sumFloat xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_sum_after_division (n : Nat) (x : Nat) (arr : List Int) : Float := sorry

theorem min_sum_properties_le_orig_sum {n : Nat} {x : Nat} {arr : List Int} 
  (h1 : x ≥ 2) (h2 : arr.length = n) (h3 : arr.length > 0) 
  (h4 : x ≠ 0) :
  min_sum_after_division n x arr ≤ Float.ofInt (List.sum arr) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_sum_properties_exists_real {n : Nat} {x : Nat} {arr : List Int}
  (h1 : x ≥ 2) (h2 : arr.length = n) (h3 : arr.length > 0) 
  (h4 : x ≠ 0) :
  ∃ r : Float, min_sum_after_division n x arr = r := sorry

theorem min_sum_properties_le_divided_sum {n : Nat} {x : Nat} {arr : List Int} {i j : Nat}
  (h1 : x ≥ 2) (h2 : arr.length = n) (h3 : arr.length > 0)
  (h4 : i ≤ j) (h5 : j < arr.length) (h6 : x ≠ 0) :
  let divided_section := (arr.drop i).take (j-i+1) |>.map (fun a => Float.ofInt a / Float.ofNat x)
  let divided_sum := Float.ofInt (List.sum (arr.take i)) + 
                    List.sumFloat divided_section +
                    Float.ofInt (List.sum (arr.drop (j+1)))
  min_sum_after_division n x arr ≤ divided_sum := sorry

theorem positive_array_nonneg {n : Nat} {x : Nat} {arr : List Int}
  (h1 : x ≥ 2) (h2 : arr.length = n) (h3 : arr.length > 0)
  (h4 : ∀ a ∈ arr, a ≥ 0) (h5 : x ≠ 0) :
  min_sum_after_division n x arr ≥ 0 := sorry 

theorem positive_array_le_sum {n : Nat} {x : Nat} {arr : List Int}
  (h1 : x ≥ 2) (h2 : arr.length = n) (h3 : arr.length > 0) 
  (h4 : ∀ a ∈ arr, a ≥ 0) (h5 : x ≠ 0) :
  min_sum_after_division n x arr ≤ Float.ofInt (List.sum arr) := sorry
-- </vc-theorems>