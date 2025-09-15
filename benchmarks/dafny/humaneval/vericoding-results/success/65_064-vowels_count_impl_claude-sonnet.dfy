// <vc-preamble>
function is_vowel(c: char): bool
  ensures is_vowel(c) <==> c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added lemma to prove set cardinality preservation */
lemma VowelSetLemma(s: string, i: int, count: int)
  requires 0 <= i < |s|
  requires count == |(set j | 0 <= j < i && is_vowel(s[j]))|
  ensures count + (if is_vowel(s[i]) then 1 else 0) == |(set j | 0 <= j < i + 1 && is_vowel(s[j]))|
{
  var oldSet := set j | 0 <= j < i && is_vowel(s[j]);
  var newSet := set j | 0 <= j < i + 1 && is_vowel(s[j]);
  
  if is_vowel(s[i]) {
    assert newSet == oldSet + {i};
    assert i !in oldSet;
  } else {
    assert newSet == oldSet;
  }
}
// </vc-helpers>

// <vc-spec>
method vowel_count(s: string) returns (count: int)

  ensures count >= 0
  ensures count == |(set i | 0 <= i < |s| && is_vowel(s[i]))| + if |s| > 0 && s[|s| - 1] == 'y' then 1 else 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added lemma call to prove invariant maintenance */
  count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == |(set j | 0 <= j < i && is_vowel(s[j]))|
  {
    VowelSetLemma(s, i, count);
    if is_vowel(s[i]) {
      count := count + 1;
    }
    i := i + 1;
  }
  if |s| > 0 && s[|s| - 1] == 'y' {
    count := count + 1;
  }
}
// </vc-code>
