-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_path (n : Nat) (vectors : List (Int × Int)) : List Int :=
  sorry

def compute_final_position (vectors : List (Int × Int)) (path : List Int) : Int × Int :=
  sorry

def verify_path_length (x : Int) (y : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_path_correct_length {n : Nat} {vectors : List (Int × Int)} :
  let path := find_path n vectors
  n = vectors.length → path.length = n :=
sorry

theorem find_path_valid_elements {n : Nat} {vectors : List (Int × Int)} :
  let path := find_path n vectors
  n = vectors.length → ∀ x ∈ path, x = 1 ∨ x = -1 :=
sorry

theorem find_path_bounded_result {n : Nat} {vectors : List (Int × Int)} :
  let path := find_path n vectors
  let final_pos := compute_final_position vectors path
  n = vectors.length →
  verify_path_length final_pos.1 final_pos.2 = true :=
sorry

theorem single_vector_axis_bounded {n : Nat} :
  n > 0 → n ≤ 50 →
  let vectors := List.replicate n (1000000, 0)
  let path := find_path n vectors
  let final_pos := compute_final_position vectors path
  verify_path_length final_pos.1 final_pos.2 = true :=
sorry
-- </vc-theorems>