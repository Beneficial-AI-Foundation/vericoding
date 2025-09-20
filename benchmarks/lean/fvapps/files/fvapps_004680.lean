-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digitsSum (n : Nat) : Nat :=
sorry

def is_valid (n : Nat) : Bool :=
sorry

def get_next (n : Nat) : Nat :=
sorry

def get_series (count start : Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem harshad_property {n : Nat} (h : n > 0) (valid : is_valid n = true) :
  n % digitsSum n = 0 :=
sorry

theorem get_next_properties {n : Nat} :
  let next := get_next n
  next > n ∧
  is_valid next = true ∧
  ∀ x, n < x → x < next → is_valid x = false :=
sorry

theorem get_series_properties {count start : Nat} (h : count > 0) :
  let series := get_series count start
  List.length series = count ∧
  (∀ i, i + 1 < List.length series →
    series[i]'(by sorry) < series[i+1]'(by sorry)) ∧
  (∀ x ∈ series, x > start) ∧
  (∀ x ∈ series, is_valid x = true) :=
sorry

theorem next_harshad_valid {n : Nat} :
  is_valid (get_next n) = true :=
sorry
-- </vc-theorems>