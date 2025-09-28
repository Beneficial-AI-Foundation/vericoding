// <vc-preamble>
function is_vowel(c: char): bool
  ensures is_vowel(c) <==> c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helper needed; provide trivial lemma to satisfy placeholder */
lemma TrivialHelper() {}

// </vc-helpers>

// <vc-spec>
method vowel_count(s: string) returns (count: int)

  ensures count >= 0
  ensures count == |(set i | 0 <= i < |s| && is_vowel(s[i]))| + if |s| > 0 && s[|s| - 1] == 'y' then 1 else 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): simple loop counting vowels via set cardinality invariant */
  var i := 0;
  count := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == |(set j | 0 <= j < i && is_vowel(s[j]))|
    decreases |s| - i
  {
    i := i + 1;
    count := |(set j | 0 <= j < i && is_vowel(s[j]))|;
  }
  if |s| > 0 && s[|s| - 1] == 'y' {
    count := count + 1;
  }
}

// </vc-code>
