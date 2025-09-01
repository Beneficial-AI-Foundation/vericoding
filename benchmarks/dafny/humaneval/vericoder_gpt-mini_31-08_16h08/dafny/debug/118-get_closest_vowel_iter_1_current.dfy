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
// No helpers needed
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
  var idx := |word| - 2;
  // invariant: for all j > idx and j < |word|-1, the pattern does not hold
  while idx >= 1
    invariant forall j :: idx < j < |word|-1 ==>
                !(IsVowel(word[j]) && IsConsonant(word[j - 1]) && IsConsonant(word[j + 1]))
    decreases idx + 2
  {
    if IsVowel(word[idx]) && IsConsonant(word[idx - 1]) && IsConsonant(word[idx + 1]) {
      return word[idx..idx+1];
    }
    idx := idx - 1;
  }
  return "";
}
// </vc-code>

