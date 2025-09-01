

// <vc-helpers>
// No changes needed in vc-helpers
// </vc-helpers>

// <vc-spec>
method vowel_count(s: string) returns (count: int)
  // post-conditions-start
  ensures count >= 0
  ensures count == |(set i | 0 <= i < |s| && is_vowel(s[i]))| + if |s| > 0 && s[|s| - 1] == 'y' then 1 else 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == |(set j | 0 <= j < i && is_vowel(s[j]))|
  {
    if is_vowel(s[i]) {
      count := count + 1;
    }
    i := i + 1;
  }
  if |s| > 0 && s[|s| - 1] == 'y' {
    count := count + 1;
  }
  return count;
}
// </vc-code>

function is_vowel(c: char): bool
  ensures is_vowel(c) <==> c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// pure-end