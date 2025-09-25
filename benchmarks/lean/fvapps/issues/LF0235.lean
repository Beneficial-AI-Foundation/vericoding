-- <vc-preamble>
def largest_vals_from_labels (values: List Int) (labels: List Int) (numWanted: Nat) (useLimit: Nat) : Int :=
  sorry

def List.sum : List Int → Int 
  | [] => 0
  | x::xs => x + List.sum xs

def myMax (a b : Int) : Int :=
  if a ≥ b then a else b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.maximum : List Int → Int
  | [] => 0
  | [x] => x
  | x::xs => myMax x (List.maximum xs)
-- </vc-definitions>

-- <vc-theorems>
theorem largest_vals_sum_bound (values: List Int) (labels: List Int) (numWanted: Nat) (useLimit: Nat)
  (h1: values.length = labels.length)
  (h2: numWanted > 0)
  (h3: useLimit > 0) :
  largest_vals_from_labels values labels numWanted useLimit ≤ 
    (List.sum (values.filter (λ x => x > 0))) :=
  sorry

theorem largest_vals_nonneg (values: List Int) (labels: List Int) (numWanted: Nat) (useLimit: Nat)
  (h1: values.length = labels.length)
  (h2: numWanted > 0)
  (h3: useLimit > 0)
  (h4: ∀ x ∈ values, x ≥ 0) :
  largest_vals_from_labels values labels numWanted useLimit ≥ 0 :=
  sorry

theorem largest_vals_use_limit (values: List Int) (labels: List Int) (numWanted: Nat) (useLimit: Nat)
  (h1: values.length = labels.length)
  (h2: numWanted > 0)
  (h3: useLimit > 0)
  (label: Int) : 
  let filtered := (values.zip labels).filter (λ p => p.1 = label)
  filtered.length ≤ useLimit :=
  sorry

theorem largest_vals_single_label (values: List Int) (h: values.length > 0) :
  largest_vals_from_labels values (List.replicate values.length 0) 1 1 = List.maximum values :=
  sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval largest_vals_from_labels [5, 4, 3, 2, 1] [1, 1, 2, 2, 3] 3 1

/-
info: 12
-/
-- #guard_msgs in
-- #eval largest_vals_from_labels [5, 4, 3, 2, 1] [1, 3, 3, 3, 2] 3 2

/-
info: 16
-/
-- #guard_msgs in
-- #eval largest_vals_from_labels [9, 8, 8, 7, 6] [0, 0, 0, 1, 1] 3 1
-- </vc-theorems>