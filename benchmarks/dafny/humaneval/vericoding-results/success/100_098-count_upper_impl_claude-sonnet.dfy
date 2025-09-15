// <vc-preamble>
function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): strengthened SetNoChangeLemma proof to explicitly show set equality */
predicate IsEvenIndexUpperVowel(s: string, i: int)
{
  0 <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])
}

lemma SetUnionLemma(s: string, i: int)
  requires 0 <= i < |s|
  requires i % 2 == 0 && is_upper_vowel(s[i])
  ensures |set j | 0 <= j < i + 1 && j % 2 == 0 && is_upper_vowel(s[j])| == |set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])| + 1
{
  var oldSet := set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j]);
  var newSet := set j | 0 <= j < i + 1 && j % 2 == 0 && is_upper_vowel(s[j]);
  assert newSet == oldSet + {i};
  assert i !in oldSet;
}

lemma SetNoChangeLemma(s: string, i: int)
  requires 0 <= i < |s|
  requires !(i % 2 == 0 && is_upper_vowel(s[i]))
  ensures |set j | 0 <= j < i + 1 && j % 2 == 0 && is_upper_vowel(s[j])| == |set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])|
{
  var oldSet := set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j]);
  var newSet := set j | 0 <= j < i + 1 && j % 2 == 0 && is_upper_vowel(s[j]);
  assert newSet == oldSet;
}
// </vc-helpers>

// <vc-spec>
method count_upper(s: string) returns (cnt: int)

  ensures cnt == |set i | 0 <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])|
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added explicit loop invariant maintenance and post-condition assertion */
{
  cnt := 0;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant cnt == |set j | 0 <= j < i && j % 2 == 0 && is_upper_vowel(s[j])|
  {
    if i % 2 == 0 && is_upper_vowel(s[i]) {
      SetUnionLemma(s, i);
      cnt := cnt + 1;
    } else {
      SetNoChangeLemma(s, i);
    }
    i := i + 1;
  }
  
  assert i == |s|;
  assert cnt == |set j | 0 <= j < |s| && j % 2 == 0 && is_upper_vowel(s[j])|;
}
// </vc-code>
