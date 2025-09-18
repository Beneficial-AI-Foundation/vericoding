-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def stairs (n : Int) : String :=
sorry

def step (n : Int) : String :=
sorry

def splitLines (s : String) : List String :=
sorry

def rightJustify (s : String) (width : Int) : String :=
sorry

def isDigit (c : Char) : Bool :=
sorry

def listToString (l : List Nat) : String :=
sorry

def stringContains (s : String) (c : Char) : Prop :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem stairs_empty_for_invalid_input (n : Int) :
  n < 1 → stairs n = " " :=
sorry

theorem stairs_line_count (n : Int) :
  n ≥ 1 → (splitLines (stairs n)).length = n.toNat :=
sorry

theorem stairs_line_width (n : Int) (line : String) :
  n ≥ 1 → line ∈ splitLines (stairs n) → line.length ≤ (4 * n - 1).toNat :=
sorry

theorem stairs_right_justified (n : Int) (line : String) :
  n ≥ 1 → line ∈ splitLines (stairs n) →
  line = rightJustify line (4 * n - 1) :=
sorry

theorem step_length_correct (n : Int) :
  n ≥ 1 → (splitLines (step n)).length = (2 * n - 1).toNat :=
sorry

theorem step_digits_only (n : Int) (c : Char) :
  n ≥ 1 → stringContains (step n) c → isDigit c ∨ c = ' ' :=
sorry

theorem step_sequence (n : Int) (i : Nat) :
  n ≥ 1 → i < n.toNat →
  let nums := splitLines (step n);
  let expected := toString ((i + 1) % 10);
  nums.get? i = some expected :=
sorry
-- </vc-theorems>