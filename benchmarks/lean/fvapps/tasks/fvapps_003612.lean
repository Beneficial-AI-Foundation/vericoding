-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def histogram (lst : List Nat) (width : Nat) : List Nat := sorry

def sum (lst : List Nat) : Nat :=
  match lst with
  | [] => 0
  | h :: t => h + sum t
-- </vc-definitions>

-- <vc-theorems>
theorem histogram_empty (width : Nat) :
  histogram [] width = [] := sorry

theorem histogram_length (lst : List Nat) (width : Nat) (h : width > 0) :
  lst ≠ [] →
  List.length (histogram lst width) = 
    (List.foldl (fun acc x => Nat.max acc (x / width)) 0 lst) + 1 := sorry

theorem histogram_sum_equals_length (lst : List Nat) (width : Nat) (h : width > 0) :
  sum (histogram lst width) = List.length lst := sorry

theorem histogram_counts_nonneg (lst : List Nat) (width : Nat) (h : width > 0) :
  ∀ x ∈ histogram lst width, x ≥ 0 := sorry

theorem histogram_bin_counts (lst : List Nat) (width : Nat) (h : width > 0) :
  ∀ bin_idx < List.length (histogram lst width),
    (histogram lst width).get ⟨bin_idx, by sorry⟩ =
      List.length (List.filter (fun x => x / width = bin_idx) lst) := sorry
-- </vc-theorems>