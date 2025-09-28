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
  /* code modified by LLM (iteration 2): fixed invariant by tracking set explicitly */
  cnt := 0;
  var i := 0;
  ghost var seen_set := {};
  while i < |s|
    invariant 0 <= i <= |s|
    invariant seen_set == set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])
    invariant cnt == |seen_set|
  {
    if i % 2 == 0 && is_upper_vowel(s[i]) {
      cnt := cnt + 1;
      seen_set := seen_set + {i};
    }
    i := i + 1;
  }
}
// </vc-code>
