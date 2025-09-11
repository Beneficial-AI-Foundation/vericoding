-- <vc-preamble>
def List.max (l: List Nat) : Nat :=
  sorry

def intToStr (n: Nat) : String :=
  sorry

def strLen (s: String) : Nat :=
  sorry

def splitLines (s: String) : List String :=
  sorry

def stringToNat (s: String) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def print_nums (nums: List Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem print_nums_empty (nums: List Nat) :
  nums = [] → print_nums nums = "" :=
  sorry
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible