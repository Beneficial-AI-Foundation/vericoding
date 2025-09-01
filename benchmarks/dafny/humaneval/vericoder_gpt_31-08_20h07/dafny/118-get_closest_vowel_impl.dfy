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

// </vc-helpers>

// <vc-spec>
method get_closest_vowel(word: string) returns (result: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |word| ==> ('A' <= word[i] <= 'Z' || 'a' <= word[i] <= 'z')
  // pre-conditions-end
  // post-conditions-start
  ensures |result| <= 1
  ensures |result| == 1 ==> IsVowel(result[0])
  ensures |result| == 1 ==> exists i {:trigger word[i]} ::
        1 <= i && i + 1 < |word|
            && IsVowel(word[i]) && IsConsonant(word[i - 1]) && IsConsonant(word[i + 1])
            && (forall j :: i < j < |word| - 1 ==> !IsVowel(word[j]) || !IsConsonant(word[j - 1]) || !IsConsonant(word[j + 1]))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |word|;
  if n < 3 {
    result := "";
    return;
  }
  var j := n - 2;
  while 1 <= j
    invariant 0 <= j <= n - 2
    invariant forall t :: j < t < n - 1 ==> !IsVowel(word[t]) || !IsConsonant(word[t - 1]) || !IsConsonant(word[t + 1])
    decreases j
  {
    if IsVowel(word[j]) && IsConsonant(word[j - 1]) && IsConsonant(word[j + 1]) {
      result := word[j..j+1];
      return;
    }
    j := j - 1;
  }
  result := "";
}
// </vc-code>

