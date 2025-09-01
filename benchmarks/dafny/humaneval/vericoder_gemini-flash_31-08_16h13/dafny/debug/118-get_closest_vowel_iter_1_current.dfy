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
lemma lemma_is_vowel_or_consonant(c: char)
  ensures ('A' <= c <= 'Z' || 'a' <= c <= 'z') ==> (IsVowel(c) || IsConsonant(c))
{
  if ('A' <= c <= 'Z' || 'a' <= c <= 'z') {
    if IsVowel(c) {
      // Do nothing, already proved
    } else {
      assert IsConsonant(c);
    }
  }
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
  var n := |word];
  var closest_vowel_char: char := ' ';
  var closest_vowel_found := false;

  var i := 1;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant !closest_vowel_found ==> closest_vowel_char == ' '
    invariant closest_vowel_found ==> IsVowel(closest_vowel_char)
    invariant forall k :: 0 <= k < i ==> ! (
        IsVowel(word[k]) && IsConsonant(word[k - 1]) && IsConsonant(word[k + 1])
    ) || !closest_vowel_found
  {
    if !closest_vowel_found {
      if IsVowel(word[i]) {
        if IsConsonant(word[i - 1]) && IsConsonant(word[i + 1]) {
          closest_vowel_char := word[i];
          closest_vowel_found := true;
        }
      }
    }
    i := i + 1;
  }

  if closest_vowel_found {
    result := "" + closest_vowel_char;
    assert |result| == 1;
    assert IsVowel(result[0]);
    var k := 0;
    while k < n - 1
      invariant 0 <= k <= n - 1
    {
      lemma_is_vowel_or_consonant(word[k]);
      k := k + 1;
    }
  } else {
    result := "";
  }
}
// </vc-code>

