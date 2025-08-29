function IsVowel(c: char) : bool
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
  c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
function IsConsonant(c: char) : bool
{
  ('A' <= c <= 'Z' || 'a' <= c <= 'z') && !IsVowel(c)
}

// <vc-helpers>
function CountConsonantsFromRight(s: string, pos: int): int
  requires 0 <= pos < |s|
{
  var count := 0;
  var i := |s| - 1;
  while i >= pos
    decreases i
    invariant -1 <= i <= |s| - 1
    invariant count >= 0
  {
    if IsConsonant(s[i]) then count := count + 1;
    i := i - 1;
  }
  count
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def get_closest_vowel(s : str) -> str
You are given a word. Your task is to find the closest vowel that stands between two consonants from the right side of the word (case sensitive).
*/
// </vc-description>

// <vc-spec>
method GetClosestVowel(s: string) returns (result: string)
  requires |s| > 0
  ensures result == "" || (|result| == 1 && IsVowel(result[0]))
  ensures result != "" ==> exists i :: 0 <= i < |s| && s[i] == result[0] && 
    exists j1, j2 :: 0 <= j1 < i < j2 < |s| && IsConsonant(s[j1]) && IsConsonant(s[j2])
// </vc-spec>
// <vc-code>
{
  var i := |s| - 1;
  while i >= 0
    decreases i
    invariant -1 <= i <= |s| - 1
  {
    if i - 1 >= 0 && i + 1 < |s| && IsConsonant(s[i - 1]) && IsVowel(s[i]) && IsConsonant(s[i + 1]) {
      return s[i..i+1];
    }
    i := i - 1;
  }
  return "";
}
// </vc-code>
