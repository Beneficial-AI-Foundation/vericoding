-- <vc-preamble>
def is_valid_time (hours mins: Nat) : Prop :=
  hours < 24 ∧ mins < 60
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_latest_time (digits: List Nat) : String :=
  sorry

def is_valid_time_str (s: String) : Bool :=
  sorry

def time_to_minutes (time: String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_latest_time_gives_valid_result {digits: List Nat}
  (h1: digits.length = 4)
  (h2: ∀ d ∈ digits, d ≤ 9) :
  is_valid_time_str (find_latest_time digits) = true :=
sorry

theorem find_latest_time_invalid_when_all_large {digits: List Nat}
  (h1: digits.length = 4)
  (h2: (∀ d ∈ digits, d ≥ 6) ∨ (∀ d ∈ digits, d > 2)) :
  find_latest_time digits = "" :=
sorry

theorem find_latest_time_zeros {digits: List Nat}
  (h1: digits.length = 4)
  (h2: ∀ d ∈ digits, d = 0) :
  find_latest_time digits = "00:00" :=
sorry

theorem find_latest_time_is_maximum {digits: List Nat} {result: String}
  (h1: digits.length = 4)
  (h2: ∀ d ∈ digits, d ≤ 9)
  (h3: result = find_latest_time digits)
  (h4: result ≠ "") :
  ∀ (h1 h2 m1 m2: Nat),
  h1 ∈ digits → h2 ∈ digits → m1 ∈ digits → m2 ∈ digits →
  is_valid_time (h1 * 10 + h2) (m1 * 10 + m2) →
  time_to_minutes result ≥ (h1 * 10 + h2) * 60 + (m1 * 10 + m2) :=
sorry
-- </vc-theorems>