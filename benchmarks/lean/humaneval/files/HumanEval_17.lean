/- 
function_signature: "def parse_music(music_string: str) -> List[int]"
docstring: |
    Input to this function is a string representing musical notes in a special ASCII format.
    Your task is to parse this string and return list of integers corresponding to how many beats does each
    not last.

    Here is a legend:
    'o' - whole note, lasts four beats
    'o|' - half note, lasts two beats
    '.|' - quater note, lasts one beat
test_cases:
  - input: "o o| .| o| o| .| .| .| .| o o"
    expected_output: [4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4]
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String) : List Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: String → List Nat)
-- inputs
(string: String) :=
-- spec
let not_map := fun
  | "o" => 4
  | "o|" => 2
  | ".|" => 1
  | _ => 0;
let spec (result: List Nat) :=
let space_split := string.splitOn " ";
space_split.length = result.length ∧
∀ i < result.length, not_map (space_split.get! i) = result.get! i;
-- program termination
∃ result, implementation string = result ∧
spec result

theorem correctness
(string: String)
: problem_spec implementation string
:=
-- <vc-proof>
  sorry
-- </vc-proof>

#test implementation "o o| .| o| o| .| .| .| .| o o" = [4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4]