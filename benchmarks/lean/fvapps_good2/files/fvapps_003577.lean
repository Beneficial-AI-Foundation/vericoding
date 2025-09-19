-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def name_file (fmt: String) (nbr: Int) (start: Int) : List String :=
  sorry

def containsIndexNo (s: String) : Bool :=
  sorry

def containsNumber (s: String) (n: Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem name_file_length
  (fmt: String) (nbr: Int) (start: Int)
  (h1: nbr > 0) (h2: nbr ≤ 1000) (h3: start ≥ -1000) (h4: start ≤ 1000) :
  (name_file fmt nbr start).length = nbr := by
sorry

theorem name_file_index_numbers
  (fmt: String) (nbr: Int) (start: Int)
  (h1: nbr > 0) (h2: nbr ≤ 1000) (h3: start ≥ -1000) (h4: start ≤ 1000)
  (h5: containsIndexNo fmt = true) :
  ∀ (i: Nat), i < nbr →
    containsNumber (List.get! (name_file fmt nbr start) i) (start + i) = true := by
sorry

theorem name_file_no_index
  (fmt: String) (nbr: Int) (start: Int)
  (h1: nbr > 0) (h2: nbr ≤ 1000) (h3: start ≥ -1000) (h4: start ≤ 1000)
  (h5: containsIndexNo fmt = false) :
  ∀ (x: String), x ∈ name_file fmt nbr start → x = fmt := by
sorry

theorem name_file_invalid_number
  (fmt: String) (nbr: Int) (start: Int)
  (h1: nbr ≤ 0) :
  name_file fmt nbr start = [] := by
sorry
-- </vc-theorems>