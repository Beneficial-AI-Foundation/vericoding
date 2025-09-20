-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_array (n : Nat) (ops : List (Nat × Nat × Nat × Int)) : (String × Option (List Int)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_array_valid_result (n : Nat) (ops : List (Nat × Nat × Nat × Int)) 
  (h : n > 0) :
  let (result, arr) := find_array n ops
  result = "YES" ∨ result = "NO" :=
sorry

theorem find_array_array_length (n : Nat) (ops : List (Nat × Nat × Nat × Int))
  (h : n > 0) :
  let (result, arr) := find_array n ops
  result = "YES" → arr.isSome ∧ arr.get!.length = n :=
sorry

theorem find_array_type1_ops (n : Nat) (ops : List (Nat × Nat × Nat × Int))
  (h : n > 0) :
  let (result, arr) := find_array n ops
  result = "YES" →
  arr.isSome →
  ∀ op ∈ ops, 
    let (t, l, r, x) := op
    t = 1 →
    l ≤ r ∧ r ≤ n →
    ∀ j : Fin arr.get!.length, l - 1 ≤ j.val ∧ j.val ≤ r - 1 →
    arr.get!.get j = arr.get!.get j + x :=
sorry

theorem find_array_type2_ops (n : Nat) (ops : List (Nat × Nat × Nat × Int))
  (h : n > 0) :
  let (result, arr) := find_array n ops
  result = "YES" →
  arr.isSome →
  ∀ op ∈ ops,
    let (t, l, r, x) := op
    t = 2 →
    l ≤ r ∧ r ≤ n →
    (∃ j : Fin arr.get!.length, l - 1 ≤ j.val ∧ j.val ≤ r - 1 ∧ arr.get!.get j = x) ∧
    ∀ j : Fin arr.get!.length, l - 1 ≤ j.val ∧ j.val ≤ r - 1 → arr.get!.get j ≤ x :=
sorry

theorem find_array_single_query (n : Nat) (x : Int)
  (h : n > 0) :
  let ops := [(2, 1, n, x)]
  let (result, arr) := find_array n ops
  result = "YES" ∧ 
  arr.isSome ∧
  ∀ i : Fin arr.get!.length, arr.get!.get i = x :=
sorry

theorem find_array_empty_ops (n : Nat)
  (h : n > 0) :
  let (result, arr) := find_array n []
  result = "YES" ∧
  arr.isSome ∧
  arr.get!.length = n ∧
  ∀ i : Fin arr.get!.length, arr.get!.get i = 10^9 :=
sorry
-- </vc-theorems>