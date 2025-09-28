// <vc-preamble>
function is_vowel(c: char): bool
  ensures is_vowel(c) <==> c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Helper lemma to prove set cardinality property when adding one element */
lemma vowel_set_lemma(s: string, i: int)
  requires 0 <= i < |s|
  ensures |(set j | 0 <= j < i + 1 && is_vowel(s[j]))| == |(set j | 0 <= j < i && is_vowel(s[j]))| + (if is_vowel(s[i]) then 1 else 0)
{
  var old_set := set j | 0 <= j < i && is_vowel(s[j]);
  var new_set := set j | 0 <= j < i + 1 && is_vowel(s[j]);
  
  if is_vowel(s[i]) {
    assert new_set == old_set + {i};
    assert i !in old_set;
  } else {
    assert new_set == old_set;
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
  /* code modified by LLM (iteration 2): Added lemma call to prove loop invariant maintenance */
  count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == |(set j | 0 <= j < i && is_vowel(s[j]))|
  {
    vowel_set_lemma(s, i);
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
