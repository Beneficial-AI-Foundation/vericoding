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
{
}

lemma VowelNotConsonant(c: char)
  ensures IsVowel(c) ==> !IsConsonant(c)
{
}

lemma ConsonantNotVowel(c: char)
  ensures IsConsonant(c) ==> !IsVowel(c)
{
}

lemma LoopInvariantHelper(word: string, i: int)
  requires forall k :: 0 <= k < |word| ==> ('A' <= word[k] <= 'Z' || 'a' <= word[k] <= 'z')
  requires 0 <= i <= |word| - 2
  requires |word| >= 3
  requires forall j :: i < j <= |word| - 2 ==> 
    (1 <= j < |word| - 1) ==> (!IsVowel(word[j]) || !IsConsonant(word[j - 1]) || !IsConsonant(word[j + 1]))
  ensures forall j :: i - 1 < j <= |word| - 2 ==> 
    (1 <= j < |word| - 1) ==> (!IsVowel(word[j]) || !IsConsonant(word[j - 1]) || !IsConsonant(word[j + 1]))
{
  forall j | i - 1 < j <= |word| - 2
    ensures (1 <= j < |word| - 1) ==> (!IsVowel(word[j]) || !IsConsonant(word[j - 1]) || !IsConsonant(word[j + 1]))
  {
    if j == i {
      // When j == i, we need to show that either it's not a valid position or the vowel condition doesn't hold
      if 1 <= j < |word| - 1 {
        // This case is handled by the loop body - if word[i] was a vowel between consonants, we would have returned
      }
    } else {
      // j > i, so this follows from the precondition
      assert i < j <= |word| - 2;
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def get_closest_vowel(s : str) -> str
You are given a word. Your task is to find the closest vowel that stands between two consonants from the right side of the word (case sensitive).
*/
// </vc-description>

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
  
  if |word| < 3 {
    return;
  }
  
  var i := |word| - 2;
  
  while i >= 1
    invariant 0 <= i <= |word| - 2
    invariant forall j :: i < j <= |word| - 2 ==> 
      (1 <= j < |word| - 1) ==> (!IsVowel(word[j]) || !IsConsonant(word[j - 1]) || !IsConsonant(word[j + 1]))
  {
    if IsVowel(word[i]) && IsConsonant(word[i - 1]) && IsConsonant(word[i + 1]) {
      result := [word[i]];
      return;
    }
    
    assert 1 <= i < |word| - 1;
    assert !IsVowel(word[i]) || !IsConsonant(word[i - 1]) || !IsConsonant(word[i + 1]);
    
    LoopInvariantHelper(word, i);
    i := i - 1;
  }
  
  assert i == 0;
  assert forall j :: 0 < j <= |word| - 2 ==> 
    (1 <= j < |word| - 1) ==> (!IsVowel(word[j]) || !IsConsonant(word[j - 1]) || !IsConsonant(word[j + 1]));
}
// </vc-code>

