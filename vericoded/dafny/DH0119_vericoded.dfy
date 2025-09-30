// <vc-preamble>
function IsVowel(c: char) : bool
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
  c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
function IsConsonant(c: char) : bool
{
  ('A' <= c <= 'Z' || 'a' <= c <= 'z') && !IsVowel(c)
}
// </vc-preamble>

// <vc-helpers>
lemma SubstringChar(word: string, i: int)
  requires 0 <= i && i + 1 <= |word|
  ensures word[i..i+1][0] == word[i]
{
}

// </vc-helpers>

// <vc-spec>
method get_closest_vowel(word: string) returns (result: string)

  requires forall i :: 0 <= i < |word| ==> ('A' <= word[i] <= 'Z' || 'a' <= word[i] <= 'z')

  ensures |result| <= 1
  ensures |result| == 1 ==> IsVowel(result[0])
  ensures |result| == 1 ==> exists i {:trigger word[i]} ::
        1 <= i && i + 1 < |word|
            && IsVowel(word[i]) && IsConsonant(word[i - 1]) && IsConsonant(word[i + 1])
            && (forall j :: i < j < |word| - 1 ==> !IsVowel(word[j]) || !IsConsonant(word[j - 1]) || !IsConsonant(word[j + 1]))
// </vc-spec>
// <vc-code>
{
  var n := |word|;
  if n < 3 {
    result := "";
    return;
  }
  var i := n - 2;
  while i >= 1
    invariant 1 <= i + 1 <= n
    invariant forall j :: i + 1 <= j < n - 1 ==> !(IsVowel(word[j]) && IsConsonant(word[j - 1]) && IsConsonant(word[j + 1]))
    decreases i
  {
    if IsVowel(word[i]) && IsConsonant(word[i - 1]) && IsConsonant(word[i + 1]) {
      result := word[i..i+1];
      SubstringChar(word, i);
      return;
    }
    i := i - 1;
  }
  result := "";
}
// </vc-code>
