-- <vc-preamble>
def list_sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h :: t => h + list_sum t

def list_take (n : Nat) (l : List Nat) : List Nat :=
  match n, l with
  | 0, _ => []
  | _, [] => []
  | n+1, h :: t => h :: list_take n t

def list_replicate (n : Nat) (v : Nat) : List Nat :=
  match n with
  | 0 => []
  | n+1 => v :: list_replicate n v
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_discount_shopping (n_discounts : Nat) (discount_values : List Nat) (n_items : Nat) (item_values : List Nat) : Nat :=
  sorry

def list_sort (l : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem discount_shopping_non_negative
  (n_discounts : Nat)
  (discount_values : List Nat)
  (n_items : Nat)
  (item_values : List Nat)
  (h1 : discount_values.length = n_discounts)
  (h2 : item_values.length = n_items)
  (h3 : ∀ x ∈ discount_values, 1 ≤ x ∧ x ≤ 10)
  (h4 : ∀ x ∈ item_values, 1 ≤ x ∧ x ≤ 1000)
  (h5 : 1 ≤ n_discounts ∧ n_discounts ≤ 5)
  (h6 : 1 ≤ n_items ∧ n_items ≤ 20) :
  0 ≤ solve_discount_shopping n_discounts discount_values n_items item_values :=
sorry

theorem discount_shopping_upper_bound
  (n_discounts : Nat)
  (discount_values : List Nat)
  (n_items : Nat)
  (item_values : List Nat)
  (h1 : discount_values.length = n_discounts)
  (h2 : item_values.length = n_items)
  (h3 : ∀ x ∈ discount_values, 1 ≤ x ∧ x ≤ 10)
  (h4 : ∀ x ∈ item_values, 1 ≤ x ∧ x ≤ 1000)
  (h5 : 1 ≤ n_discounts ∧ n_discounts ≤ 5)
  (h6 : 1 ≤ n_items ∧ n_items ≤ 20) :
  solve_discount_shopping n_discounts discount_values n_items item_values ≤ list_sum item_values :=
sorry

theorem discount_shopping_min_items
  (n_discounts : Nat)
  (discount_values : List Nat)
  (n_items : Nat)
  (item_values : List Nat)
  (h1 : discount_values.length = n_discounts)
  (h2 : item_values.length = n_items)
  (h3 : ∀ x ∈ discount_values, 1 ≤ x ∧ x ≤ 10)
  (h4 : ∀ x ∈ item_values, 1 ≤ x ∧ x ≤ 1000)
  (h5 : 1 ≤ n_discounts ∧ n_discounts ≤ 5)
  (h6 : 1 ≤ n_items ∧ n_items ≤ 20) :
  let sorted_items := list_sort item_values
  let min_disc := match discount_values with
                  | [] => n_items
                  | h :: t => min h n_items
  let min_items_sum := list_sum (list_take min_disc sorted_items)
  solve_discount_shopping n_discounts discount_values n_items item_values ≥ min_items_sum :=
sorry

theorem identical_items_result
  (n_discounts : Nat)
  (n_items : Nat)
  (item_value : Nat)
  (h1 : 1 ≤ n_discounts ∧ n_discounts ≤ 5)
  (h2 : 1 ≤ n_items ∧ n_items ≤ 5)
  (h3 : 1 ≤ item_value ∧ item_value ≤ 100) :
  let discount_values := list_replicate n_discounts 2
  let item_values := list_replicate n_items item_value
  let result := solve_discount_shopping n_discounts discount_values n_items item_values
  result % item_value = 0 ∧ result ≤ item_value * n_items :=
sorry
-- </vc-theorems>