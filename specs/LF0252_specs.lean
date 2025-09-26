-- <vc-preamble>
def List.maximum (l: List Nat) : Nat :=
match l with
| [] => 0
| (x::xs) => xs.foldl Nat.max x

def List.sum (l: List Nat) : Nat :=
match l with
| [] => 0
| (x::xs) => x + xs.sum
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_eating_speed (piles : List Nat) (h : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_eating_speed_bounds {piles : List Nat} {h : Nat} (hpiles : piles ≠ []) 
  (hpile_bounds : ∀ x ∈ piles, 1 ≤ x ∧ x ≤ 10^4) (hh : 1 ≤ h ∧ h ≤ 10^4)
  (hlen : piles.length ≤ h) :
  let k := min_eating_speed piles h
  1 ≤ k ∧ k ≤ List.maximum piles :=
sorry

theorem min_eating_speed_finishes {piles : List Nat} {h : Nat} (hpiles : piles ≠ [])
  (hlen : piles.length ≤ h) :
  let k := min_eating_speed piles h
  let hours_needed := List.sum (piles.map (fun p => (p + k - 1) / k))
  hours_needed ≤ h :=
sorry

theorem min_eating_speed_minimal {piles : List Nat} {h : Nat} (hpiles : piles ≠ [])
  (hlen : piles.length ≤ h) :
  let k := min_eating_speed piles h
  k > 1 →
  let slower := k - 1
  let hours_slower := List.sum (piles.map (fun p => (p + slower - 1) / slower))
  hours_slower > h :=
sorry

theorem min_eating_speed_truly_minimal {piles : List Nat} {h : Nat} 
  (hpiles : piles ≠ []) (hlen : piles.length ≤ h)
  (hpile_bounds : ∀ x ∈ piles, 1 ≤ x ∧ x ≤ 100) (hh : 1 ≤ h ∧ h ≤ 5) :
  let k := min_eating_speed piles h
  ∀ i, 1 ≤ i → i < k →
  let hours := List.sum (piles.map (fun p => (p + i - 1) / i))
  hours > h :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval min_eating_speed [3, 6, 7, 11] 8

/-
info: 30
-/
-- #guard_msgs in
-- #eval min_eating_speed [30, 11, 23, 4, 20] 5

/-
info: 23
-/
-- #guard_msgs in
-- #eval min_eating_speed [30, 11, 23, 4, 20] 6
-- </vc-theorems>