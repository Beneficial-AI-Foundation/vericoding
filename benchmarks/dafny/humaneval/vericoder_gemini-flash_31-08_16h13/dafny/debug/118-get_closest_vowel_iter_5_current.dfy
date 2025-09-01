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
  var closest_vowel_index: int := -1;

  var i := 1;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant !closest_vowel_found ==> closest_vowel_char == ' ' && closest_vowel_index == -1
    invariant closest_vowel_found ==> (IsVowel(closest_vowel_char) && closest_vowel_index >= 1 && closest_vowel_index + 1 < n
                                    && IsVowel(word[closest_vowel_index]) && IsConsonant(word[closest_vowel_index - 1]) && IsConsonant(word[closest_vowel_index + 1])
                                    && closest_vowel_char == word[closest_vowel_index])
    invariant forall k :: 1 <= k < i ==> ! (
        IsVowel(word[k]) && IsConsonant(word[k - 1]) && IsConsonant(word[k + 1])
    ) || (closest_vowel_found && (exists m :: 1 <= m < i && m == closest_vowel_index
                                        && IsVowel(word[m]) && IsConsonant(word[m-1]) && IsConsonant(word[m+1])
                                        && word[m] == closest_vowel_char ))
  {
    if !closest_vowel_found {
      if IsVowel(word[i]) {
        if i >= 1 && i + 1 < n { // Ensure valid indices for word[i-1] and word[i+1]
          lemma_is_vowel_or_consonant(word[i-1]);
          lemma_is_vowel_or_consonant(word[i+1]);
          if IsConsonant(word[i - 1]) && IsConsonant(word[i + 1]) {
            closest_vowel_char := word[i];
            closest_vowel_found := true;
            closest_vowel_index := i;
          }
        }
      }
    }
    i := i + 1;
  }

  if closest_vowel_found {
    result := [closest_vowel_char];
  } else {
    result := "";
  }
}
// </vc-code>

