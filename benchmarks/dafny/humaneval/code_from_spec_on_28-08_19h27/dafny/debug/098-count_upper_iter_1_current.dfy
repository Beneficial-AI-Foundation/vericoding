// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def count_upper(s : String) -> Int
Given a string s, count the number of uppercase vowels in even indices.
*/
// </vc-description>

// <vc-spec>
method count_upper(s: string) returns (count: int)
  ensures count >= 0
  ensures count <= |s|
  ensures count == |set i | 0 <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])|
// </vc-spec>
// <vc-code>
{
  count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count >= 0
    invariant count == |set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])|
  {
    if i % 2 == 0 && is_upper_vowel(s[i]) {
      count := count + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// pure-end