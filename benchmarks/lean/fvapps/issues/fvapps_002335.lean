-- <vc-preamble>
def calculate_average_salary (salaries : List Nat) : Float := sorry

def isUnique (l : List Nat) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_to_float (n : Nat) : Float := sorry

def insertSort (l : List Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem average_salary_between_min_max 
  (salaries : List Nat)
  (h1 : salaries.length ≥ 3)
  (h2 : isUnique salaries) : 
  match salaries.minimum?, salaries.maximum? with
  | some min, some max => 
      let result := calculate_average_salary salaries
      list_to_float min ≤ result ∧ result ≤ list_to_float max
  | _, _ => True
  := sorry

theorem average_salary_matches_expected
  (salaries : List Nat)
  (h1 : salaries.length ≥ 3)
  (h2 : isUnique salaries) :
  let sorted := insertSort salaries
  let expected := list_to_float (sorted.get? 1).get! + 
                  list_to_float (sorted.get? (sorted.length - 2)).get! / 2
  Float.abs (calculate_average_salary salaries - expected) < 1e-10 :=
sorry

theorem average_salary_order_invariant
  (salaries shuffled : List Nat)
  (h1 : salaries.length ≥ 3)
  (h2 : isUnique salaries)
  (h3 : shuffled.length = salaries.length)
  (h4 : ∀ x, x ∈ salaries ↔ x ∈ shuffled) :
  Float.abs (calculate_average_salary salaries - calculate_average_salary shuffled) < 1e-10 :=
sorry
-- </vc-theorems>