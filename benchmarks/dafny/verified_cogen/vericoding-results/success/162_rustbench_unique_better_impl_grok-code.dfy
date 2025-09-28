// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 5): simplified implementation to remove duplicates from non-decreasing array with proper invariants */
  var res: seq<int> := [];
  var i: int := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k, m :: 0 <= k < m < |res| ==> res[k] < res[m]
    invariant forall k :: 0 <= k < |res| ==> exists j :: 0 <= j < i && res[k] == a[j]
    invariant |res| <= i
  {
    if i == 0 || a[i] != a[i-1] {
      res := res + [a[i]];
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>
