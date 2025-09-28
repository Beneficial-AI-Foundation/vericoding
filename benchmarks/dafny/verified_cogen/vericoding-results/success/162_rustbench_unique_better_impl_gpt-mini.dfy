// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): strictness predicate */
predicate StrictSeq(s: seq<int>) { forall i: int, j: int :: 0 <= i && i < j && j < |s| ==> s[i] < s[j] }
// </vc-helpers>

// <vc-spec>
method UniqueBetter(a: array<int>) returns (result: seq<int>)
    requires
        forall i: int, j: int ::
            0 <= i && i < j && j < a.Length ==> a[i] <= a[j]
    ensures
        forall i: int, j: int ::
            0 <= i && i < j && j < |result| ==> result[i] < result[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build unique strictly increasing sequence from non-decreasing array */
  var res: seq<int> := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i && i <= a.Length
    invariant forall p: int, q: int :: 0 <= p && p < q && q < |res| ==> res[p] < res[q]
    invariant |res| <= i
    invariant forall k: int :: 0 <= k && k < |res| ==> exists idx: int :: 0 <= idx && idx < i && a[idx] == res[k]
  {
    if |res| == 0 || res[|res|-1] < a[i] {
      res := res + [a[i]];
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>
