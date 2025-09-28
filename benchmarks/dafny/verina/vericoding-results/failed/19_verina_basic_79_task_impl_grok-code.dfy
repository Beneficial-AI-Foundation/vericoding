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
for i := 0 to x {
  if a[i] > m || i == 0 {
    m := a[i];
  }
}
var p := x;
while p < a.Length - 1 && a[p] <= m {
  p := p + 1;
}
result := (m, p);
}
// </vc-code>
