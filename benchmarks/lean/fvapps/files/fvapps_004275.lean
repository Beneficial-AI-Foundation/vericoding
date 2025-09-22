-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsPowerOfTwo (n : Nat) : Bool :=
  sorry

def validateRhythm (meter : List Nat) (score : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem validate_rhythm_result_options (meter : List Nat) (score : String) :
  let result := validateRhythm meter score;
  result = "Valid rhythm" ∨ result = "Valid rhythm with anacrusis" ∨ result = "Invalid rhythm" :=
sorry

theorem validate_rhythm_valid_bars_sum (meter : List Nat) (score : String)
  (h1 : meter.length = 2) (h2 : meter[0]! > 0) (h3 : meter[1]! > 0)
  (h4 : let result := validateRhythm meter score;
        result = "Valid rhythm" ∨ result = "Valid rhythm with anacrusis") :
  let bars := score.splitOn "|";
  ∀ bar ∈ bars.tail.dropLast, bar ≠ "" →
  ∃ barSum target : Nat,
    barSum = target ∧ target = meter[0]! / meter[1]! :=
sorry

theorem validate_rhythm_invalid_meter_denom (meter : List Nat)
  (h1 : meter.length = 2)
  (h2 : meter[1]! > 0)
  (h3 : ¬(IsPowerOfTwo meter[1]!)) :
  validateRhythm meter "4|4" = "Invalid rhythm" :=
sorry
-- </vc-theorems>