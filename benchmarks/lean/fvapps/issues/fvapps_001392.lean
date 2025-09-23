-- <vc-preamble>
def count_collisions (n m : Nat) (likes : List String) : Nat :=
  sorry

def List.sum (xs : List Nat) : Nat :=
  xs.foldl (· + ·) 0

/- Helper function to get character from string at position -/
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getChar? (s : String) (i : Nat) : Option Char :=
  s.data.get? i
-- </vc-definitions>

-- <vc-theorems>
theorem count_collisions_nonnegative {n m : Nat} {likes : List String} :
  count_collisions n m likes ≥ 0 :=
  sorry 

/- Helper function to sum a list of natural numbers -/

theorem count_collisions_formula {n m : Nat} {likes : List String} :
  count_collisions n m likes = 
    let colSums := List.range m |>.map (fun col => 
      List.range n |>.filter (fun row => 
        match likes.get? row with
        | none => false
        | some s => match getChar? s col with
          | some '1' => true
          | _ => false
      ) |>.length);
    colSums.map (fun ones => ones * (ones - 1) / 2) |>.sum :=
  sorry

theorem count_collisions_zeros {n m : Nat} {likes : List String}
  (h : ∀ i j, i < n → j < m → 
    match likes.get? i with
    | none => true
    | some s => getChar? s j = some '0') :
  count_collisions n m likes = 0 :=
  sorry

theorem count_collisions_all_ones {n : Nat} {likes : List String}
  (h : ∀ i, i < n → 
    match likes.get? i with
    | none => true 
    | some s => getChar? s 0 = some '1') :
  count_collisions n 1 likes = n * (n - 1) / 2 :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_collisions 4 3 ["111", "100", "110", "000"]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_collisions 2 2 ["10", "01"]

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_collisions 3 2 ["11", "11", "11"]
-- </vc-theorems>