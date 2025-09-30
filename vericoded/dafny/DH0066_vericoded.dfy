// <vc-preamble>
function is_vowel(c: char): bool
  ensures is_vowel(c) <==> c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): vowel_prefix_count defined via set cardinality */
function vowel_prefix_count(s: string, n: int): int
  requires 0 <= n <= |s|
{
  |(set k | 0 <= k < n && is_vowel(s[k]))|
}

// </vc-helpers>

// <vc-spec>
method vowel_count(s: string) returns (count: int)

  ensures count >= 0
  ensures count == |(set i | 0 <= i < |s| && is_vowel(s[i]))| + if |s| > 0 && s[|s| - 1] == 'y' then 1 else 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): compute count using vowel_prefix_count and handle trailing 'y' */
  var i := 0;
  var vcount := vowel_prefix_count(s, 0);
  while i < |s|
    invariant 0 <= i <= |s|
    invariant vcount >= 0
    invariant vcount == vowel_prefix_count(s, i)
    decreases |s| - i
  {
    vcount := vowel_prefix_count(s, i+1);
    i := i + 1;
  }
  if |s| > 0 && s[|s| - 1] == 'y' {
    count := vcount + 1;
  } else {
    count := vcount;
  }
}

// </vc-code>
