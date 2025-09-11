-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_updown_length (n : Nat) (arr : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_updown_length_bounds {n : Nat} {arr : List Int} 
    (h_size : arr.length = n) (h_n : n ≥ 2) :
  let result := find_updown_length n arr
  2 ≤ result ∧ result ≤ n + 1 :=
sorry

theorem find_updown_length_monotonic {n : Nat} {arr : List Int}
    (h_size : arr.length = n) (h_n : n ≥ 2)
    (h_monotonic : ∀ i, i < n - 1 → arr[i]! < arr[i+1]!) :
  find_updown_length n arr ≥ n :=
sorry

theorem find_updown_length_extension {n : Nat} {arr : List Int}
    (h_size : arr.length = n) (h_n : n ≥ 2) :
  let arr2 := arr.append [arr.getLast!]
  find_updown_length (n+1) arr2 ≥ find_updown_length n arr - 1 :=
sorry

theorem find_updown_length_binary {n : Nat} {arr : List Int}
    (h_size : arr.length = n) (h_n : n ≥ 2)
    (h_binary : ∀ x ∈ arr, x = 1 ∨ x = 2) :
  find_updown_length n arr ≥ (n + 1) / 2 :=
sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval find_updown_length 7 [100, 1, 10, 3, 20, 25, 24]

/-
info: 6
-/
-- #guard_msgs in
-- #eval find_updown_length 5 [3, 3, 2, 4, 1]

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_updown_length 4 [1, 2, 1, 3]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded