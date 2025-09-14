// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple min helper */
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method insertion_sort(l: array<int>) returns (result: array<int>)
    ensures
        /* The result is sorted in non-decreasing order */
        forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]
    ensures
        /* The result is a permutation of the input */
        result.Length == l.Length && multiset(result[..]) == multiset(l[..])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): insertion sort using immutable sequences */
  var n := l.Length;
  var s: seq<int> := [];
  var idx := 0;
  while idx < n
    invariant 0 <= idx <= n
    invariant s.Length == idx
    invariant forall p, q :: 0 <= p < q < s.Length ==> s[p] <= s[q]
    invariant multiset(s) == multiset(l[..idx])
  {
    var v := l[idx];
    var pos := 0;
    while pos < s.Length && s[pos] <= v
      invariant 0 <= pos <= s.Length
      invariant forall p, q :: 0 <= p < q < pos ==> s[p] <= s[q]
      invariant forall p :: 0 <= p < pos ==> s[p] <= v
    {
      pos := pos + 1;
    }
    s := s[..pos] + [v] + s[pos..];
    idx := idx + 1;
  }

  result := new int[n];
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant forall p :: 0 <= p < k ==> result[p] == s[p]
  {
    result[k] := s[k];
    k := k + 1;
  }
}
// </vc-code>
