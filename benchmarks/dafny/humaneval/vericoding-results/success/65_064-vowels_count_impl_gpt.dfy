// <vc-preamble>
function is_vowel(c: char): bool
  ensures is_vowel(c) <==> c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): lemma to relate set cardinalities when extending the scanned prefix by one position */
lemma CardinalityExtend(s: string, i: int)
  requires 0 <= i < |s|
  ensures |(set j | 0 <= j < i + 1 && is_vowel(s[j]))| ==
          |(set j | 0 <= j < i && is_vowel(s[j]))| + (if is_vowel(s[i]) then 1 else 0)
{
  if is_vowel(s[i]) {
    assert i !in (set j | 0 <= j < i && is_vowel(s[j]));
    assert (set j | 0 <= j < i + 1 && is_vowel(s[j])) ==
           (set j | 0 <= j < i && is_vowel(s[j])) + {i};
    assert |(set j | 0 <= j < i && is_vowel(s[j])) + {i}| ==
           |(set j | 0 <= j < i && is_vowel(s[j]))| + 1;
  } else {
    assert (set j | 0 <= j < i + 1 && is_vowel(s[j])) ==
           (set j | 0 <= j < i && is_vowel(s[j]));
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
  /* code modified by LLM (iteration 3): iterative scan with non-ghost saved index and lemma application to maintain set-cardinality invariant */
  var c := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant c == |(set j | 0 <= j < i && is_vowel(s[j]))|
    invariant c >= 0
  {
    var preI := i;
    if is_vowel(s[preI]) {
      c := c + 1;
    }
    assert c == |(set j | 0 <= j < preI && is_vowel(s[j]))| + (if is_vowel(s[preI]) then 1 else 0);
    CardinalityExtend(s, preI);
    assert c == |(set j | 0 <= j < preI + 1 && is_vowel(s[j]))|;
    i := preI + 1;
  }
  count := c + (if |s| > 0 && s[|s| - 1] == 'y' then 1 else 0);
}
// </vc-code>
