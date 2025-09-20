-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def paint_letterboxes (start: Nat) (finish: Nat) : List Nat :=
sorry

def str_count_digits (n: Nat) : List Nat :=
sorry

def toString (n: Nat) : String :=
sorry

def sum_list (l: List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem paint_letterboxes_range {start finish : Nat} (h: start ≤ finish) :
  let result := paint_letterboxes start finish
  List.length result = 10 ∧
  (∀ x ∈ result, x ≥ 0) :=
sorry

theorem paint_letterboxes_single_number (n: Nat) :
  paint_letterboxes n n = str_count_digits n :=
sorry

theorem paint_letterboxes_zero :
  paint_letterboxes 0 0 = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0] :=
sorry

theorem paint_letterboxes_non_negative {a b : Nat} :
  ∀ x ∈ paint_letterboxes a b, x ≥ 0 :=
sorry
-- </vc-theorems>