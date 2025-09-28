// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no change, reviewed for correctness */
method ComputeMaxPrefix(a: array<int>, x: int) returns (m: int)
  requires a.Length > 0 && 0 < x <= a.Length
  ensures forall k :: 0 <= k < x ==> a[k] <= m
  ensures exists k :: 0 <= k < x && a[k] == m
{
  m := a[0];
  var i := 1;
  while i < x
    invariant 1 <= i <= x
    invariant forall k :: 0 <= k < i ==> a[k] <= m
    invariant exists k :: 0 <= k < i && a[k] == m
  {
    if a[i] > m {
      m := a[i];
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method OnlineMax(a: array<int>, x: int) returns (result: (int, int))
    requires
        a.Length > 0 &&
        x < a.Length
    ensures
        var (m, p) := result;
        x <= p && p < a.Length &&
        (forall i :: 0 <= i < x ==> a[i] <= m) &&
        (exists i :: 0 <= i < x && a[i] == m) &&
        ((p < a.Length - 1) ==> (exists i :: x <= i <= p && a[i] > m)) &&
        ((forall i :: x <= i < a.Length ==> a[i] <= m) ==> p == a.Length - 1)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): guarded call to helper and handled contradictory spec for x<=0 */
  if x > 0 {
    var m := ComputeMaxPrefix(a, x);

    var j := x;
    while j < a.Length
      invariant x <= j <= a.Length
      invariant forall k :: 0 <= k < x ==> a[k] <= m
      invariant exists k :: 0 <= k < x && a[k] == m
      invariant forall k :: x <= k < j ==> a[k] <= m
    {
      if a[j] > m {
        result := (m, j);
        return;
      }
      j := j + 1;
    }
    result := (m, a.Length - 1);
  } else {
    // For x <= 0, the ensures clause `exists i :: 0 <= i < x && a[i] == m` is false.
    // This path cannot be satisfied, indicating a contradiction in the specification for this input range.
    assert false;
  }
}
// </vc-code>
