

// <vc-helpers>
lemma VowelSetCardinality(s: string, i: int)
  requires 0 <= i <= |s|
  ensures |(set j | 0 <= j < i && is_vowel(s[j]))| <= i
{
}

lemma VowelSetIncremental(s: string, i: int)
  requires 0 <= i < |s|
  ensures if is_vowel(s[i]) then
    |(set j | 0 <= j < i + 1 && is_vowel(s[j]))| == |(set j | 0 <= j < i && is_vowel(s[j]))| + 1
  else
    |(set j | 0 <= j < i + 1 && is_vowel(s[j]))| == |(set j | 0 <= j < i && is_vowel(s[j]))|
{
  var set1 := set j | 0 <= j < i && is_vowel(s[j]);
  var set2 := set j | 0 <= j < i + 1 && is_vowel(s[j]);
  
  if is_vowel(s[i]) {
    assert set2 == set1 + {i};
    assert i !in set1;
  } else {
    assert set2 == set1;
  }
}
// </vc-helpers>

// <vc-spec>
method vowel_count(s: string) returns (count: int)
  // post-conditions-start
  ensures count >= 0
  ensures count == |(set i | 0 <= i < |s| && is_vowel(s[i]))| + if |s| > 0 && s[|s| - 1] == 'y' then 1 else 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  count := 0;
  var vowel_set_count := 0;
  
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant vowel_set_count == |(set j | 0 <= j < i && is_vowel(s[j]))|
    invariant vowel_set_count >= 0
  {
    if is_vowel(s[i]) {
      vowel_set_count := vowel_set_count + 1;
    }
    VowelSetIncremental(s, i);
    i := i + 1;
  }
  
  count := vowel_set_count;
  if |s| > 0 && s[|s| - 1] == 'y' {
    count := count + 1;
  }
}
// </vc-code>

function is_vowel(c: char): bool
  ensures is_vowel(c) <==> c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// pure-end