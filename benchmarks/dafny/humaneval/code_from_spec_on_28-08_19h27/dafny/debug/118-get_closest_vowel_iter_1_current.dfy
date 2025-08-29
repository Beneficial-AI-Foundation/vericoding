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
function HasConsonantToLeft(s: string, i: int): bool
  requires 0 <= i < |s|
{
  i > 0 && IsConsonant(s[i-1])
}

function HasConsonantToRight(s: string, i: int): bool
  requires 0 <= i < |s|
{
  i < |s| - 1 && IsConsonant(s[i+1])
}

function IsVowelBetweenConsonants(s: string, i: int): bool
  requires 0 <= i < |s|
{
  IsVowel(s[i]) && HasConsonantToLeft(s, i) && HasConsonantToRight(s, i)
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
  ensures |result| <= 1
  ensures |result| == 1 ==> IsVowel(result[0])
  ensures |result| == 0 ==> (forall i :: 0 <= i < |s| ==> !IsVowelBetweenConsonants(s, i))
  ensures |result| == 1 ==> (exists i :: 0 <= i < |s| && IsVowelBetweenConsonants(s, i) && result[0] == s[i])
// </vc-spec>
// <vc-code>
{
  if |s| < 3 {
    return "";
  }
  
  var i := |s| - 2;
  while i > 0
    invariant 0 <= i <= |s| - 2
    invariant forall j :: i < j < |s| - 1 ==> !IsVowelBetweenConsonants(s, j)
  {
    if IsVowelBetweenConsonants(s, i) {
      return [s[i]];
    }
    i := i - 1;
  }
  
  return "";
}
// </vc-code>
