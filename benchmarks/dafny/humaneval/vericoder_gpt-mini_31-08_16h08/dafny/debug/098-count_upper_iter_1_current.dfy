

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method count_upper(s: string) returns (cnt: int)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 0;
  cnt := 0;
  while i < |s|
    invariant 0 <= i <= |s|;
    invariant cnt == |set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])|;
    decreases |s| - i;
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