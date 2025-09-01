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
lemma CharToStringIsVowel(c: char)
  requires IsVowel(c)
  ensures IsVowel([c][0])
{
}

lemma SingleCharStringLength(c: char)
  ensures |[c]| == 1
{
}

lemma EmptyStringLength()
  ensures |""| == 0
{
}

lemma VowelConsonantProperties(word: string, i: int)
  requires 0 <= i < |word|
  requires forall k :: 0 <= k < |word| ==> ('A' <= word[k] <= 'Z' || 'a' <= word[k] <= 'z')
  ensures IsVowel(word[i]) ==> ('A' <= word[i] <= 'Z' || 'a' <= word[i] <= 'z')
  ensures IsConsonant(word[i]) ==> ('A' <= word[i] <= 'Z' || 'a' <= word[i] <= 'z')
{
}
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
  if |word| < 3 {
    return "";
  }
  
  var i := |word| - 2;
  while i >= 1
    invariant 0 <= i <= |word| - 2
    invariant forall j :: i < j < |word| - 1 ==> !IsVowel(word[j]) || !IsConsonant(word[j - 1]) || !IsConsonant(word[j + 1])
  {
    if IsVowel(word[i]) && IsConsonant(word[i - 1]) && IsConsonant(word[i + 1]) {
      CharToStringIsVowel(word[i]);
      SingleCharStringLength(word[i]);
      return [word[i]];
    }
    i := i - 1;
  }
  
  EmptyStringLength();
  return "";
}
// </vc-code>

