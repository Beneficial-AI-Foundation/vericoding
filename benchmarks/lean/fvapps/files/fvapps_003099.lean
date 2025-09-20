-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rearranger (k : Nat) (nums : List Nat) : String :=
sorry

def splitString (s : String) (sep : String) : List String :=
sorry

def trim (s : String) : String :=
sorry

def toNat! (s : String) : Nat :=
sorry

def getFirst (l : List α) : α :=
sorry

def replace (s : String) (target : String) (replacement : String) : String :=
sorry

def sortString (s : String) : String :=
sorry

def joinStrings (l : List String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rearranger_divisible (k : Nat) (nums : List Nat) :
  k > 0 → nums.length > 0 →
  let result := rearranger k nums
  result ≠ "There is no possible rearrangement" →
  let parts := splitString result "generates:"
  let numberStr := getFirst (splitString (getFirst (parts.tail)) "divisible by")
  let number := toNat! (trim numberStr)
  number % k = 0 :=
sorry

theorem rearranger_preserves_digits (k : Nat) (nums : List Nat) :
  k > 0 → nums.length > 0 →
  let result := rearranger k nums
  result ≠ "There is no possible rearrangement" →
  let input_digits := nums.map toString |> joinStrings |> sortString
  let parts := splitString result "generates:"
  let first_part := trim (replace (getFirst parts) "Rearrangement:" "")
  let result_digits := splitString first_part ", " |> joinStrings |> sortString
  input_digits = result_digits :=
sorry
-- </vc-theorems>