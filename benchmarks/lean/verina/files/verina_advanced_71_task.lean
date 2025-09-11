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

/-
-- Invalid Inputs
[
    {
        "input": {
            "s": "2",
            "k": 1
        }
    }
]
-- Tests
[
    {
        "input": {
            "s": "100011001",
            "k": 3
        },
        "expected": "11001",
        "unexpected": [
            "00011",
            "10001",
            ""
        ]
    },
    {
        "input": {
            "s": "1011",
            "k": 2
        },
        "expected": "11",
        "unexpected": [
            "101",
            "01",
            ""
        ]
    },
    {
        "input": {
            "s": "000",
            "k": 1
        },
        "expected": "",
        "unexpected": [
            "0",
            "00",
            "000"
        ]
    },
    {
        "input": {
            "s": "11111",
            "k": 3
        },
        "expected": "111",
        "unexpected": [
            "11",
            "1111",
            ""
        ]
    },
    {
        "input": {
            "s": "10100101",
            "k": 2
        },
        "expected": "101",
        "unexpected": [
            "010",
            "1001",
            "0101"
        ]
    },
    {
        "input": {
            "s": "1001001",
            "k": 2
        },
        "expected": "1001",
        "unexpected": [
            "0010",
            "0100",
            "001"
        ]
    },
    {
        "input": {
            "s": "10010001",
            "k": 1
        },
        "expected": "1",
        "unexpected": [
            "10",
            "100",
            "000"
        ]
    },
    {
        "input": {
            "s": "1001",
            "k": 0
        },
        "expected": "0",
        "unexpected": [
            "10",
            "100",
            "1"
        ]
    }
]
-/