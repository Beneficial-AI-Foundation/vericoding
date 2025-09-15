// <vc-preamble>
function is_upper_vowel(c: char) : bool {
  c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Extracted the set comprehension into a helper function to aid verification. */
function CountedSet(s: string, k: int): set<int>
  requires 0 <= k <= |s|
{
  set i | 0 <= i < k && i % 2 == 0 && is_upper_vowel(s[i])
}

/* helper modified by LLM (iteration 3): Added a lemma to relate CountedSet at steps i and i+1. */
lemma CountedSet_InductiveStep(s: string, i: int)
  requires 0 <= i < |s|
  ensures CountedSet(s, i + 1) == CountedSet(s, i) + (if i % 2 == 0 && is_upper_vowel(s[i]) then {i} else {})
{
}
// </vc-helpers>

// <vc-spec>
method count_upper(s: string) returns (cnt: int)

  ensures cnt == |set i | 0 <= i < |s| && i % 2 == 0 && is_upper_vowel(s[i])|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Called the helper lemma to aid the loop invariant proof. */
  cnt := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant cnt == |CountedSet(s, i)|
  {
    if i % 2 == 0 && is_upper_vowel(s[i]) {
      CountedSet_InductiveStep(s, i);
      cnt := cnt + 1;
    } else {
      CountedSet_InductiveStep(s, i);
    }
    i := i + 1;
  }
}
// </vc-code>
