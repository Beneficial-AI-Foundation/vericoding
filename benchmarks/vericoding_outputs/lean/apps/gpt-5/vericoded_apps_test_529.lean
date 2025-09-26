import Mathlib
-- <vc-preamble>
def ValidInput (s : String) (n : Int) : Prop :=
  0 ≤ n ∧ n ≤ 26

def GetComparisonChar (n : Int) : Char :=
  let alphabet := ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', '|']
  alphabet[n.natAbs]!

def IsLowercase (c : Char) : Bool :=
  'a' ≤ c && c ≤ 'z'

def IsUppercase (c : Char) : Bool :=
  'A' ≤ c && c ≤ 'Z'

def ToLowercase (c : Char) : Char :=
  if IsUppercase c then Char.ofNat (c.toNat - 'A'.toNat + 'a'.toNat)
  else c

def ToUppercase (c : Char) : Char :=
  if IsLowercase c then Char.ofNat (c.toNat - 'a'.toNat + 'A'.toNat)
  else c

def ToLowercaseString (s : String) : String :=
  s.map ToLowercase

def TransformWithCompChar (s : String) (compChar : Char) : String :=
  s.map (fun c => if c < compChar then ToUppercase c else c)

def TransformString (s : String) (n : Int) : String :=
  let compChar := GetComparisonChar n
  TransformWithCompChar (ToLowercaseString s) compChar

@[reducible, simp]
def solve_precond (s : String) (n : Int) : Prop :=
  ValidInput s n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma solve_precond_iff (s : String) (n : Int) :
  solve_precond s n ↔ ValidInput s n := Iff.rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (n : Int) (h_precond : solve_precond s n) : String :=
  TransformString s n
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (n : Int) (result : String) (h_precond : solve_precond s n) : Prop :=
  result = TransformString s n

theorem solve_spec_satisfied (s : String) (n : Int) (h_precond : solve_precond s n) :
    solve_postcond s n (solve s n h_precond) h_precond := by
  simp [solve_postcond, solve]
-- </vc-theorems>
