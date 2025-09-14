// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reverse index function and range lemma to reason about indices */
function revIndex(i: int, n: int): int { n - 1 - i }
lemma RevIndexInRange(i: int, n: int)
  requires 0 <= i < n
  ensures 0 <= revIndex(i, n) < n
{ }
// </vc-helpers>

// <vc-spec>
method ReverseString(s: array<char>) returns (result: array<char>)
    ensures
        result.Length == s.Length &&
        forall i :: 0 <= i < s.Length ==> result[i] == s[s.Length - 1 - i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): reversed string by filling array with mirrored indices; removed redundant null invariant to avoid warning */
  var n := s.Length;
  result := new char[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall k :: 0 <= k < i ==> result[k] == s[n - 1 - k]
    decreases n - i
  {
    // ensure the source index is in range
    assert 0 <= n - 1 - i;
    assert n - 1 - i < n;
    result[i] := s[n - 1 - i];
    i := i + 1;
  }
}
// </vc-code>
