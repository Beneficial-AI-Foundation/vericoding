/- 
{
  "name": "numpy.typecodes",
  "category": "Miscellaneous Type Utilities",
  "description": "Dictionary mapping strings to corresponding type character codes",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.typecodes.html",
  "doc": "typecodes : dict\n\nA dictionary with string keys that represent NumPy dtype categories and string values that contain type codes for the NumPy data types in each category.\n\nKeys include:\n- 'Character': 'S1'\n- 'Integer': 'bhilqnp'\n- 'UnsignedInteger': 'BHILQNP'\n- 'Float': 'fdg'\n- 'Complex': 'FDG'\n- 'AllInteger': 'bBhHiIlLqQnNpP'\n- 'AllFloat': 'fdgFDG'\n- 'Datetime': 'Mm'\n- 'All': '?bhilqnpBHILQNPfdgFDGSUVOMm'\n\nThis is useful for iterating over all dtypes of a certain kind.\n\nExamples\n--------\n>>> np.typecodes['Character']\n'S1'\n>>> for typechar in np.typecodes['Integer']:\n...     print(typechar)\n...\nb\nh\ni\nl\nq\nn\np",
}
-/

/-  Returns the type character codes for a given NumPy dtype category -/

/-  Specification: typecodes returns the correct type character codes for each NumPy dtype category -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def typecodes (category : String) : Id (Option String) :=
  sorry

theorem typecodes_spec (category : String) :
    ⦃⌜True⌝⦄
    typecodes category
    ⦃⇓result => ⌜
      (category = "Character" → result = some "S1") ∧
      (category = "Integer" → result = some "bhilqnp") ∧
      (category = "UnsignedInteger" → result = some "BHILQNP") ∧
      (category = "Float" → result = some "fdg") ∧
      (category = "Complex" → result = some "FDG") ∧
      (category = "AllInteger" → result = some "bBhHiIlLqQnNpP") ∧
      (category = "AllFloat" → result = some "fdgFDG") ∧
      (category = "Datetime" → result = some "Mm") ∧
      (category = "All" → result = some "?bhilqnpBHILQNPfdgFDGSUVOMm") ∧
      (category ∉ ["Character", "Integer", "UnsignedInteger", "Float", "Complex", "AllInteger", "AllFloat", "Datetime", "All"] → result = none)
    ⌝⦄ := by
  sorry
