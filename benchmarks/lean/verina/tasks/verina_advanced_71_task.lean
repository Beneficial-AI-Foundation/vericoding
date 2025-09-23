-- <vc-preamble>
@[reducible]
def shortestBeautifulSubstring_precond (s : String) (k : Nat) : Prop :=
  s.toList.all (fun c => c = '0' ∨ c = '1')
-- </vc-preamble>

-- <vc-helpers>
def countOnes (lst : List Char) : Nat :=
  lst.foldl (fun acc c => if c = '1' then acc + 1 else acc) 0

def listToString (lst : List Char) : String :=
  String.mk lst
def isLexSmaller (a b : List Char) : Bool :=
  listToString a < listToString b
def allSubstrings (s : List Char) : List (List Char) :=
  let n := s.length
  (List.range n).flatMap (fun i =>
    (List.range (n - i)).map (fun j =>
      s.drop i |>.take (j + 1)))
-- </vc-helpers>

-- <vc-definitions>
def shortestBeautifulSubstring (s : String) (k : Nat) (h_precond : shortestBeautifulSubstring_precond (s) (k)) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def shortestBeautifulSubstring_postcond (s : String) (k : Nat) (result: String) (h_precond : shortestBeautifulSubstring_precond (s) (k)) : Prop :=
  let chars := s.data
  let substrings := (List.range chars.length).flatMap (fun i =>
    (List.range (chars.length - i + 1)).map (fun len =>
      chars.drop i |>.take len))
  let isBeautiful := fun sub => countOnes sub = k
  let beautiful := substrings.filter (fun sub => isBeautiful sub)
  let targets := beautiful.map (·.asString) |>.filter (fun s => s ≠ "")
  (result = "" ∧ targets = []) ∨
  (result ∈ targets ∧
   ∀ r ∈ targets, r.length ≥ result.length ∨ (r.length = result.length ∧ result ≤ r))

theorem shortestBeautifulSubstring_spec_satisfied (s: String) (k: Nat) (h_precond : shortestBeautifulSubstring_precond (s) (k)) :
    shortestBeautifulSubstring_postcond (s) (k) (shortestBeautifulSubstring (s) (k) h_precond) h_precond := by
  sorry
-- </vc-theorems>