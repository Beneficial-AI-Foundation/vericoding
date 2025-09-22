-- <vc-preamble>
def GenerateSquares : List Int :=
  List.range 44721 |>.map (fun i => Int.ofNat (i + 1) * Int.ofNat (i + 1))

def IsSubsequenceHelper (pattern : String) (text : String) (pIdx : Nat) (tIdx : Nat) : Bool :=
  if pIdx >= pattern.length then true
  else if tIdx >= text.length then false
  else if pattern.data[pIdx]? = text.data[tIdx]? ∧ pattern.data[pIdx]? ≠ none then
    IsSubsequenceHelper pattern text (pIdx + 1) (tIdx + 1)
  else
    IsSubsequenceHelper pattern text pIdx (tIdx + 1)
termination_by text.length - tIdx

def IsSubsequence (pattern : String) (text : String) : Bool :=
  IsSubsequenceHelper pattern text 0 0

def IntToStringHelper (n : Nat) : String :=
  if n < 10 then String.mk [Char.ofNat (n + 48)]
  else IntToStringHelper (n / 10) ++ String.mk [Char.ofNat (n % 10 + 48)]
termination_by n

def IntToString (n : Int) : String :=
  if n = 0 then "0"
  else if n < 0 then "-" ++ IntToStringHelper n.natAbs
  else IntToStringHelper n.natAbs

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  s.length > 0 ∧ 
  (∀ i, i < s.length → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9') ∧
  (s.data[0]! ≠ '0' ∨ s.length = 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : Int) (h_precond : solve_precond s) : Prop :=
  (result = -1 ∨ result ≥ 0) ∧
  (result = -1 → ∀ sq, sq ∈ GenerateSquares → ¬IsSubsequence (IntToString sq) s) ∧
  (result ≥ 0 → ∃ sq, sq ∈ GenerateSquares ∧ IsSubsequence (IntToString sq) s ∧ result = Int.ofNat s.length - Int.ofNat (IntToString sq).length) ∧
  (result ≥ 0 → ∀ sq, sq ∈ GenerateSquares ∧ IsSubsequence (IntToString sq) s → Int.ofNat s.length - Int.ofNat (IntToString sq).length ≥ result)

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>