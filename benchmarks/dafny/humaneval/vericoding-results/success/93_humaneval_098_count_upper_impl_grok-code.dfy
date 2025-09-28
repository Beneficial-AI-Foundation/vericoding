// <vc-preamble>
function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method count_upper(s: string) returns (cnt: int)

  ensures cnt == |set i | 0 <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Add ghost set to verify count invariant */
  cnt := 0;
  ghost var myset := {};
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant myset == set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])
    invariant cnt == |myset|
  {
    if i % 2 == 0 && is_upper_vowel(s[i]) {
      cnt := cnt + 1;
      myset := myset + {i};
    }
    i := i + 1;
  }
  
}
// </vc-code>
