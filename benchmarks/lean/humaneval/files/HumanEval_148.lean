/- 
function_signature: "def bf(planet1: str, planet2: str) -> List[str]"
docstring: |
    There are eight planets in our solar system: the closest to the Sun
    is Mercury, the next one is Venus, then Earth, Mars, Jupiter, Saturn,
    Uranus, Neptune.
    Write a function that takes two planet names as strings planet1 and planet2.
    The function should return a tuple containing all planets whose orbits are
    located between the orbit of planet1 and the orbit of planet2, sorted by
    the proximity to the sun.
    The function should return an empty tuple if planet1 or planet2
    are not correct planet names.
test_cases:
  - input: ("Jupiter", "Neptune")
    expected_output: ("Saturn", "Uranus")
  - input: ("Earth", "Mercury")
    expected_output: ("Venus")
  - input: ("Mercury", "Uranus")
    expected_output: ("Venus", "Earth", "Mars", "Jupiter", "Saturn")
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (planet1: String) (planet2: String) : List String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: String → String → List String)
-- inputs
(planet1: String)
(planet2: String) :=
-- spec
let spec (result: List String) :=
let planets := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"];
if planet1 ∉ planets ∨ planet2 ∉ planets then
  result = []
else
  let index1 := planets.idxOf planet1;
  let index2 := planets.idxOf planet2;
  let minIdx := if index1 < index2 then index1 else index2;
  let maxIdx := if index1 < index2 then index2 else index1;
  (∀ str ∈ result, str ∈ planets) ∧
  (∀ planet ∈ planets, planet ∈ result ↔
    planets.idxOf planet < maxIdx ∧
    minIdx < planets.idxOf planet) ∧
  result.Sorted (fun a b => planets.idxOf a < planets.idxOf b)
-- program termination
∃ result, impl planet1 planet2 = result ∧
-- return value satisfies spec
spec result

theorem correctness
(planet1: String)
(planet2: String)
: problem_spec implementation planet1 planet2 :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "Jupiter" "Neptune" = ["Saturn", "Uranus"]
-- #test implementation "Earth" "Mercury" = ["Venus"]
-- #test implementation "Mercury" "Uranus" = ["Venus", "Earth", "Mars", "Jupiter", "Saturn"]