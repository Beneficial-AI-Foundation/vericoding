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
function HasValidVowelPosition(word: string, i: int): bool
  requires 0 <= i < |word|
  requires forall k :: 0 <= k < |word| ==> ('A' <= word[k] <= 'Z' || 'a' <= word[k] <= 'z')
{
  1 <= i && i + 1 < |word| &&
  IsVowel(word[i]) && IsConsonant(word[i - 1]) && IsConsonant(word[i + 1])
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
method GetClosestVowel(word: string) returns (result: string)
  requires forall i :: 0 <= i < |word| ==> ('A' <= word[i] <= 'Z' || 'a' <= word[i] <= 'z')
  ensures |result| <= 1
  ensures |result| == 1 ==> IsVowel(result[0])
  ensures |result| == 1 ==> exists i {:trigger word[i]} ::
        1 <= i && i + 1 < |word|
            && IsVowel(word[i]) && IsConsonant(word[i - 1]) && IsConsonant(word[i + 1])
            && (forall j :: i < j < |word| - 1 ==> !IsVowel(word[j]) || !IsConsonant(word[j - 1]) || !IsConsonant(word[j + 1]))
{
  result := "";
  if |word| < 3 {
    return;
  }
  var i := 1;
  while i < |word| - 1
    invariant 1 <= i <= |word| - 1
    invariant forall k :: 1 <= k < i ==> !HasValidVowelPosition(word, k)
  {
    if IsVowel(word[i]) && IsConsonant(word[i - 1]) && IsConsonant(word[i + 1]) {
      result := [word[i]];
      assert HasValidVowelPosition(word, i);
      var j := i + 1;
      while j < |word| - 1
        invariant i < j <= |word| - 1
        invariant forall k :: i < k < j ==> !HasValidVowelPosition(word, k)
      {
        j := j + 1;
      }
      assert forall k :: i < k < |word| - 1 ==> !HasValidVowelPosition(word, k);
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
