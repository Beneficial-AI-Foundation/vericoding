

// <vc-helpers>
// This section is left empty as no additional helpers are needed.
// </vc-helpers>

// <vc-spec>
method count_upper(s: string) returns (cnt: int)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  cnt := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant cnt == |{ k: int | 0 <= k < i && k % 2 == 0 && is_upper_vowel(s[k]) :: k }|
  {
    if i % 2 == 0 && is_upper_vowel(s[i]) {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// pure-end