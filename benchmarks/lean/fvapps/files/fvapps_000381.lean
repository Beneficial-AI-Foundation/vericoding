-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getMaxRepetitions (s1: String) (n1: Nat) (s2: String) (n2: Nat) : Nat :=
  sorry

def is_subsequence (s1 s2: String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_non_negative (s1: String) (n1: Nat) (s2: String) (n2: Nat) :
  getMaxRepetitions s1 n1 s2 n2 ≥ 0 :=
sorry

theorem result_positive_implies_common_chars (s1: String) (n1: Nat) (s2: String) (n2: Nat) :
  getMaxRepetitions s1 n1 s2 n2 > 0 → ∃ c, c ∈ s2.data ∧ c ∈ s1.data :=
sorry

theorem monotonic_in_n1 (s1: String) (n1: Nat) (s2: String) (n2: Nat) :
  getMaxRepetitions s1 (n1 + 1) s2 n2 ≥ getMaxRepetitions s1 n1 s2 n2 :=
sorry

theorem monotonic_in_s1_length (s1: String) (n1: Nat) (s2: String) (n2: Nat)
  (h1: s1.length > 0) (h2: s2.length > 0) :
  getMaxRepetitions (s1 ++ s1) n1 s2 n2 ≥ getMaxRepetitions s1 n1 s2 n2 :=
sorry

theorem same_string_division (s: String) :
  getMaxRepetitions s 3 s 2 = 3 / 2 :=
sorry

theorem impossible_match (s1: String) (n1: Nat) :
  (∀ c, c ∈ s1.data → c ≠ 'c') →
  getMaxRepetitions s1 n1 "c" 1 = 0 :=
sorry
-- </vc-theorems>