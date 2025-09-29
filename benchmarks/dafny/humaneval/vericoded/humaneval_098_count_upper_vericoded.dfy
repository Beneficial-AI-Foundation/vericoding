// <vc-preamble>
function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Changed to ghost function returning set of indices instead of count */
ghost function UpperVowelEvenIndices(s: string, n: nat): set<int>
  requires n <= |s|
{
  set i | 0 <= i < n && i % 2 == 0 && is_upper_vowel(s[i])
}
// </vc-helpers>

// <vc-spec>
method count_upper(s: string) returns (cnt: int)

  ensures cnt == |set i | 0 <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])|
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Track set of indices instead of counter, handle idx properly */
{
  ghost var found_indices: set<int> := {};
  var idx := 0;
  cnt := 0;
  
  while idx < |s|
    invariant 0 <= idx <= |s| + 1
    invariant idx % 2 == 0 || idx == |s|
    invariant found_indices == UpperVowelEvenIndices(s, if idx > |s| then |s| else idx)
    invariant cnt == |found_indices|
  {
    if idx < |s| && is_upper_vowel(s[idx]) {
      found_indices := found_indices + {idx};
      cnt := cnt + 1;
    }
    idx := idx + 2;
  }
  
  assert found_indices == UpperVowelEvenIndices(s, |s|);
}
// </vc-code>
