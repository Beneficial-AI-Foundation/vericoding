

// <vc-helpers>
function countEvenUpperVowelsUpTo(s: string, i: nat): nat
  requires i <= |s|
{
  |set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])|
}
// </vc-helpers>

// <vc-spec>
method count_upper(s: string) returns (cnt: int)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  cnt := countEvenUpperVowelsUpTo(s, |s|);
}
// </vc-code>

function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// pure-end