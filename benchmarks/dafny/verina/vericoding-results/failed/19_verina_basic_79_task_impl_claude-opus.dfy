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
{
  var m := a[0];
  var j := 0;
  while j < x
    invariant 0 <= j <= x
    invariant forall i :: 0 <= i < j ==> a[i] <= m
    invariant exists i :: 0 <= i < j && a[i] == m
  {
    if a[j] > m {
      m := a[j];
    }
    j := j + 1;
  }
  
  var p := x;
  while p < a.Length && a[p] <= m
    invariant x <= p <= a.Length
    invariant forall i :: x <= i < p ==> a[i] <= m
  {
    p := p + 1;
  }
  
  if p < a.Length {
    p := p;
  } else {
    p := a.Length - 1;
  }
  
  result := (m, p);
}
// </vc-code>
