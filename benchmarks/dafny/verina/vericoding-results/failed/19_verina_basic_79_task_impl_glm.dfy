// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 3): fixed loop invariants by remembering the index of the maximum and handling x<=0 separately */
{
  var m, p: int;
  if x <= 0 {
    m := a[0];
    p := a.Length-1;
  } else {
    m := a[0];
    var idx := 0;
    var i := 1;
    while i < x
      invariant 1 <= i <= x
      invariant forall k :: 0 <= k < i ==> a[k] <= m
      invariant 0 <= idx < i && a[idx] == m
    {
      if a[i] > m {
        m := a[i];
        idx := i;
      }
      i := i + 1;
    }

    p := a.Length - 1;
    var j := x;
    while j < a.Length
      invariant x <= j <= a.Length
      invariant p == a.Length - 1 || (x <= p <= j && a[p] > m)
    {
      if a[j] > m {
        p := j;
        break;
      }
      j := j + 1;
    }
  }
  result := (m, p);
}
// </vc-code>
