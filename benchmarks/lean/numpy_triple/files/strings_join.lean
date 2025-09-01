/- 
{
  "name": "numpy.strings.join",
  "category": "String operations",
  "description": "Return a string which is the concatenation of the strings in the sequence seq",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.join.html",
  "doc": "Return a string which is the concatenation of the strings in the sequence \`seq\`.\n\nParameters\n----------\nsep : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nseq : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input types",
}
-/

/-  numpy.strings.join: Return a string which is the concatenation of the strings in the sequence seq.

    For each pair of separator and sequence, join the elements of the sequence using the separator.
    This function operates element-wise on vectors, where each element of the result is obtained
    by joining the corresponding elements of the sequence vector using the corresponding separator.

    The function treats each string in the sequence as a sequence of characters, and joins them
    with the separator string. For example, join('-', 'abc') produces 'a-b-c'.

    From NumPy documentation:
    - Parameters: sep (array_like) - Separator string(s), seq (array_like) - Sequence(s) to join
    - Returns: out (ndarray) - Output array with joined strings
    - Examples: join('-', 'osd') → 'o-s-d', join(['-', '.'], ['ghc', 'osd']) → ['g-h-c', 'o.s.d']

    Mathematical Properties:
    1. Element-wise operation: result[i] = join(sep[i], seq[i])
    2. Character separation: joins individual characters of each string in seq
    3. Empty separator handling: join('', s) = s (no separation)
    4. Empty sequence handling: join(sep, '') = '' (empty result)
    5. Single character sequences: join(sep, 'a') = 'a' (no separator needed)
-/

/-  Specification: numpy.strings.join returns a vector where each element is the result
    of joining the characters of the corresponding sequence element with the separator.

    This function performs element-wise string joining operations. For each index i,
    it takes the string seq[i], treats it as a sequence of characters, and joins them
    using sep[i] as the separator.

    Mathematical Properties:
    1. Element-wise correctness: For each i, result[i] is formed by joining characters
       of seq[i] with sep[i]
    2. Character-level operation: Each character in seq[i] is separated by sep[i]
    3. Empty string handling: join(sep, '') = '' for any separator
    4. Single character handling: join(sep, 'c') = 'c' (no separator added)
    5. Multiple character handling: join('-', 'abc') = 'a-b-c'
    6. Length property: For non-empty strings with length > 1, the result length is
       original_length + (original_length - 1) * separator_length
    7. Preservation of empty inputs: Empty strings remain empty regardless of separator
    8. Character order preservation: Characters appear in the same order as in input
    
    Sanity checks:
    - Result vector has same length as input vectors
    - Empty sequences produce empty results
    - Single character sequences produce the original character
    - Multiple character sequences are properly separated
    - Each result character is either from the original string or the separator
    - No characters are lost or duplicated (except separators)
    
    Precondition: True (no special preconditions for string joining)
    Postcondition: Each result element is the join of characters from the corresponding
                   sequence element using the corresponding separator, with proper
                   length and character ordering properties
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def join {n : Nat} (sep seq : Vector String n) : Id (Vector String n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem join_spec {n : Nat} (sep seq : Vector String n) :
    ⦃⌜True⌝⦄
    join sep seq
    ⦃⇓result => ⌜∀ i : Fin n, 
      let s := seq.get i
      let separator := sep.get i
      let expected_result := if s.length ≤ 1 then s 
                           else String.intercalate separator (s.toList.map String.singleton)
      -- Core correctness property
      result.get i = expected_result ∧
      -- Length property for non-trivial cases
      (s.length > 1 → (result.get i).length = s.length + (s.length - 1) * separator.length) ∧
      -- Empty string preservation
      (s.length = 0 → result.get i = "") ∧
      -- Single character preservation  
      (s.length = 1 → result.get i = s) ∧
      -- Non-empty result for non-empty input
      (s.length > 0 → (result.get i).length > 0)⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
