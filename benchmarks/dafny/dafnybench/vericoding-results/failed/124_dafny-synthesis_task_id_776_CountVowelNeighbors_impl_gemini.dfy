// <vc-preamble>
predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added predicate to aid quantifier instantiation */
predicate IsMatch(s: string, j: int)
{
    1 <= j < |s|-1 && IsVowel(s[j-1]) && IsVowel(s[j+1])
}
// </vc-helpers>

// <vc-spec>
method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): used helper predicate to fix trigger warnings */
  count := 0;
  if |s| >= 3 {
    var i := 1;
    ghost var counted_indices: set<int> := {};
    while i < |s| - 1
      invariant 1 <= i <= |s| - 1
      invariant counted_indices == (set j | 1 <= j < i && IsMatch(s, j))
      invariant count == |counted_indices|
    {
      if IsMatch(s, i) {
        counted_indices := counted_indices + {i};
        count := count + 1;
      }
      i := i + 1;
    }
  }
}
// </vc-code>
