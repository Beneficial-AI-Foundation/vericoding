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

-- <vc-helpers>
-- </vc-helpers>

def print_nums (nums: List Nat) : String :=
  sorry

theorem print_nums_empty (nums: List Nat) :
  nums = [] → print_nums nums = "" :=
  sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible