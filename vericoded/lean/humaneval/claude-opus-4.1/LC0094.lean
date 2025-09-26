-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def implementation (D: Std.HashMap String String) : Bool :=
  if D.isEmpty then
    false
  else
    let keys := D.keys
    keys.all (fun s => s.toLower = s) || keys.all (fun s => s.toUpper = s)
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: Std.HashMap String String → Bool)
-- inputs
(D: Std.HashMap String String) :=
-- spec
let spec (result : Bool) :=
  match D.isEmpty with
  | true => result = false
  | false =>
    let keys := D.keys
    let all_lower := keys.all (fun s => s.toLower = s)
    let all_upper := keys.all (fun s => s.toUpper = s)
    result = true ↔ all_lower || all_upper
-- program termination
∃ result,
  implementation D = result ∧
  spec result

theorem correctness
(D: Std.HashMap String String)
: problem_spec implementation D
:= by
  unfold problem_spec
  unfold implementation
  by_cases h : D.isEmpty
  · -- Case: D.isEmpty = true
    use false
    simp [if_pos h, h]
  · -- Case: D.isEmpty = false
    use (D.keys.all (fun s => s.toLower = s) || D.keys.all (fun s => s.toUpper = s))
    simp [if_neg h, h]
-- </vc-theorems>

-- #test implementation (Std.HashMap.ofList [("a", "apple"), ("b", "banana")]) = true
-- #test implementation (Std.HashMap.ofList [("a", "apple"), ("A", "banana"), ("B", "banana")]) = false
-- #test implementation (Std.HashMap.ofList [("a", "apple"), ("b", "banana"), ("a", "apple")]) = false
-- #test implementation (Std.HashMap.ofList [("Name", "John"), ("Age", "36"), ("City", "Houston")]) = false
-- #test implementation (Std.HashMap.ofList [("STATE", "NC"), ("ZIP", "12345")]) = true