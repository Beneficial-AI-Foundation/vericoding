import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (txt: String) : Bool :=
  sorry

def problem_spec
-- function signature
(impl: String → Bool)
-- inputs
(txt: String) :=
-- spec
let spec (result: Bool) :=
  let words := txt.splitOn " ";
  match words with
  | [] => result = False
  | [last_word] => (result ↔ last_word.length = 1 ∧ (let diff := (last_word.get 0).toLower.toNat - 'a'.toNat; 0 ≤ diff ∧ diff ≤ 25))
  | _::tail => result ↔ (let tail_txt := String.join tail; impl tail_txt);
-- program terminates
∃ result, impl txt = result ∧
-- return value satisfies spec
spec result

theorem correctness
(txt: String)
: problem_spec implementation txt := by
  sorry

-- #test implementation "apple pie" = false
-- #test implementation "apple pi e" = true
-- #test implementation "apple pi e " = false
-- #test implementation "" = false