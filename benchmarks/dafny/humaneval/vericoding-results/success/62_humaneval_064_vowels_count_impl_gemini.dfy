// <vc-preamble>
function is_vowel(c: char): bool
  ensures is_vowel(c) <==> c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method vowel_count(s: string) returns (count: int)

  ensures count >= 0
  ensures count == |(set i | 0 <= i < |s| && is_vowel(s[i]))| + if |s| > 0 && s[|s| - 1] == 'y' then 1 else 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): [fixed compilation error by removing ghost keyword from assignment] */
  count := 0;
  var i := 0;
  ghost var vowels_so_far: set<int> := {};
  while i < |s|
    invariant 0 <= i <= |s|
    invariant vowels_so_far == (set j | 0 <= j < i && is_vowel(s[j]))
    invariant count == |vowels_so_far|
  {
    if is_vowel(s[i]) {
      vowels_so_far := vowels_so_far + {i};
      count := count + 1;
    }
    i := i + 1;
  }

  if |s| > 0 && s[|s| - 1] == 'y' {
    count := count + 1;
  }
}
// </vc-code>
