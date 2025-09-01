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
  // The default postcondition for a function is `true`, unless an `ensures` clause is given.
  // The compiler would infer `IsConsonant(c)` from the `else` branch of the outermost `if`
  // statement, but not directly from this lemma. This lemma helps linking the character type
  // with the IsVowel/IsConsonant properties, which are used in the postcondition.
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
  var n := |word|;
  var closest_vowel_char: char := ' ';
  var closest_vowel_found := false;

  var i := 1;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant !closest_vowel_found ==> closest_vowel_char == ' '
    invariant closest_vowel_found ==> IsVowel(closest_vowel_char)
    invariant forall k :: 1 <= k < i ==> ! (
        IsVowel(word[k]) && IsConsonant(word[k - 1]) && IsConsonant(word[k + 1])
    ) || (closest_vowel_found && exists m :: 1 <= m < i && IsVowel(word[m]) && IsConsonant(word[m-1]) && IsConsonant(word[m+1]) && word[m] == closest_vowel_char)
  {
    if !closest_vowel_found {
      if IsVowel(word[i]) {
        if i >= 1 && i + 1 < n { // Ensure valid indices for word[i-1] and word[i+1]
          lemma_is_vowel_or_consonant(word[i-1]);
          lemma_is_vowel_or_consonant(word[i+1]);
          if IsConsonant(word[i - 1]) && IsConsonant(word[i + 1]) {
            closest_vowel_char := word[i];
            closest_vowel_found := true;
          }
        }
      }
    }
    i := i + 1;
  }

  if closest_vowel_found {
    result := "" + closest_vowel_char;
    assert |result| == 1;
    assert IsVowel(result[0]);
    // The postcondition requires a specific index `i` to be used.
    // We need to prove that such an `i` exists within the original loop and
    // its properties conform to the postcondition.
    // The invariant implies that if closest_vowel_found is true,
    // then there exists an 'm' such that the conditions are met.
    // This 'm' is the first such vowel encountered by the loop.
  } else {
    result := "";
  }
}
// </vc-code>

