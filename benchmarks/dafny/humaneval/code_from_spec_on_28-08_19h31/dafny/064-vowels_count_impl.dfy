// <vc-helpers>
function count_vowels(s: string, n: int): int
  requires 0 <= n <= |s|
  ensures count_vowels(s, n) == |(set i | 0 <= i < n && is_vowel(s[i]))| + if n == |s| && n > 0 && s[n - 1] == 'y' then 1 else 0
{
  if n == 0 then 0
  else count_vowels(s, n - 1) + (if is_vowel(s[n - 1]) then 1 else 0) + (if n == |s| && s[n - 1] == 'y' then 1 else 0)
}
// </vc-helpers>

// <vc-spec>
method vowel_count(s: string) returns (count: int)
  // post-conditions-start
  ensures count >= 0
  ensures count == |(set i | 0 <= i < |s| && is_vowel(s[i]))| + if |s| > 0 && s[|s| - 1] == 'y' then 1 else 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
method CountVowels(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |(set i | 0 <= i < |s| && is_vowel(s[i]))| + if |s| > 0 && s[|s| - 1] == 'y' then 1 else 0
{
  var n := |s|;
  var cnt := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant cnt == |(set j | 0 <= j < i && is_vowel(s[j]))|
  {
    if is_vowel(s[i]) {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  if n > 0 && s[n - 1] == 'y' {
    cnt := cnt + 1;
  }
  count := cnt;
}
// </vc-code>

function is_vowel(c: char): bool
  ensures is_vowel(c) <==> c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// pure-end