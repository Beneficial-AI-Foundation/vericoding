-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + xs.sum
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find (rats : List Nat) : Nat := sorry

theorem find_total_is_sum_of_powers (rats : List Nat) 
  (h : ∀ x, x ∈ rats → x ≤ 9) 
  (h2 : ∀ x y, x ∈ rats → y ∈ rats → x = y → x = y)
  (h3 : rats.length > 0)
  (h4 : (rats.map (fun r => 2^r)).sum ≤ 1000) :
  find rats = (rats.map (fun r => 2^r)).sum := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_binary_representation (rats : List Nat)
  (h : ∀ x, x ∈ rats → x ≤ 9)
  (h2 : ∀ x y, x ∈ rats → y ∈ rats → x = y → x = y)
  (h3 : rats.length > 0) :
  ∀ i, i ≤ 9 → 
    (if i ∈ rats 
     then (find rats).mod (2^(i+1)) ≥ 2^i
     else (find rats).mod (2^(i+1)) < 2^i) := sorry

theorem find_commutative (rats : List Nat)
  (h : ∀ x, x ∈ rats → x ≤ 9)
  (h2 : ∀ x y, x ∈ rats → y ∈ rats → x = y → x = y)
  (h3 : rats.length > 0) :
  find rats = find rats.reverse := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find [0]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find [1]

/-
info: 4
-/
-- #guard_msgs in
-- #eval find [2]

/-
info: 1000
-/
-- #guard_msgs in
-- #eval find [3, 5, 6, 7, 8, 9]

/-
info: 27
-/
-- #guard_msgs in
-- #eval find [0, 1, 3, 4]
-- </vc-theorems>