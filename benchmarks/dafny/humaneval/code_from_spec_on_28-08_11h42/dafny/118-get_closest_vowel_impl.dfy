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
lemma VowelConsonantProperties(c: char)
  requires 'A' <= c <= 'Z' || 'a' <= c <= 'z'
  ensures IsVowel(c) || IsConsonant(c)
  ensures !(IsVowel(c) && IsConsonant(c))
{
}

predicate ValidVowelPosition(word: string, i: int)
  requires 0 <= i < |word|
{
  1 <= i && i + 1 < |word| && IsVowel(word[i]) && IsConsonant(word[i - 1]) && IsConsonant(word[i + 1])
}

lemma ValidPositionImpliesVowel(word: string, i: int)
  requires 0 <= i < |word|
  requires ValidVowelPosition(word, i)
  ensures IsVowel(word[i])
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
    result := "";
    return;
  }
  
  var i := |word| - 2;
  while i >= 1
    invariant 0 <= i
    invariant forall j :: i < j < |word| - 1 ==> 
      !IsVowel(word[j]) || !IsConsonant(word[j - 1]) || !IsConsonant(word[j + 1])
  {
    if IsVowel(word[i]) && IsConsonant(word[i - 1]) && IsConsonant(word[i + 1]) {
      result := [word[i]];
      return;
    }
    i := i - 1;
  }
  
  result := "";
}
// </vc-code>
