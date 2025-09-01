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
lemma {:vcs_split_on_every_assert} ClosestVowelLemma(word: string, i: int)
  requires forall k :: 0 <= k < |word| ==> ('A' <= word[k] <= 'Z' || 'a' <= word[k] <= 'z')
  requires 1 <= i && i + 1 < |word|
  requires IsVowel(word[i]) && IsConsonant(word[i-1]) && IsConsonant(word[i+1])
  ensures exists j :: i <= j < |word| - 1 ==> 
          IsVowel(word[j]) && IsConsonant(word[j-1]) && IsConsonant(word[j+1]) &&
          (forall k :: j < k < |word| - 1 ==> !IsVowel(word[k]) || !IsConsonant(word[k-1]) || !IsConsonant(word[k+1]))
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
  result := "";
  var idx := |word| - 2;
  
  while idx >= 1
    invariant -1 <= idx < |word|
    invariant idx < |word| - 1 ==> forall j :: idx < j < |word| - 1 ==> 
              !IsVowel(word[j]) || !IsConsonant(word[j-1]) || !IsConsonant(word[j+1])
    decreases idx
  {
    if idx + 1 < |word| && IsVowel(word[idx]) && IsConsonant(word[idx-1]) && IsConsonant(word[idx+1]) {
      result := word[idx..idx+1];
      return;
    }
    idx := idx - 1;
  }
}
// </vc-code>

