-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binary_pyramid (m n : Nat) : String := sorry

theorem binary_pyramid_valid_bits (m n : Nat) :
  let result := binary_pyramid m n
  ∀ c ∈ result.toList, c = '0' ∨ c = '1' := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binary_pyramid_length_bound (m n : Nat) :
  let maxSum := (List.range (n - m + 1)).map (fun i => toString (Nat.toDigits 2 (i + m)))
                |> List.map (fun s => String.toNat! s) 
                |> List.foldl (· + ·) 0
  (binary_pyramid m n).length ≤ (toString (Nat.toDigits 2 maxSum)).length := sorry

theorem binary_pyramid_value_preservation (m n : Nat) :
  let result := binary_pyramid m n
  let maxSum := (List.range (n - m + 1)).map (fun i => toString (Nat.toDigits 2 (i + m)))
                |> List.map (fun s => String.toNat! s)
                |> List.foldl (· + ·) 0
  String.toNat! result = maxSum := sorry

theorem binary_pyramid_zero : binary_pyramid 0 0 = "0" := sorry

theorem binary_pyramid_one : binary_pyramid 1 1 = "1" := sorry

/-
info: '1111010'
-/
-- #guard_msgs in
-- #eval binary_pyramid 1 4

/-
info: '101001101'
-/
-- #guard_msgs in
-- #eval binary_pyramid 1 6

/-
info: '0'
-/
-- #guard_msgs in
-- #eval binary_pyramid 0 0
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded