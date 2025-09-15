// <vc-preamble>
function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helpers needed */

// </vc-helpers>

// <vc-spec>
method count_upper(s: string) returns (cnt: int)

  ensures cnt == |set i | 0 <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])|
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): use a set to track upper vowel positions for easier verification */
{
  var upper_positions: set<int> := {};
  for i := 0 to |s|
    invariant upper_positions == set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])
  {
    if i % 2 == 0 && is_upper_vowel(s[i]) {
      upper_positions := upper_positions + {i};
    }
  }
  cnt := |upper_positions|;
}
// </vc-code>
