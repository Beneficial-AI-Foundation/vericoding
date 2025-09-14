

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method onlineMax(a: array<int>, x: int) returns (ghost m:int, p:int)
  requires 1<=x<a.Length
  requires a.Length!=0
  ensures x<=p<a.Length
  ensures forall i::0<=i<x==> a[i]<=m
  ensures exists i::0<=i<x && a[i]==m
  ensures x<=p<a.Length-1 ==> (forall i::0<=i<p ==> a[i]<a[p])
  ensures (forall i::x<=i<a.Length && a[i]<=m) ==> p==a.Length-1
// </vc-spec>
// <vc-code>
{
  m := a[0];
  var i := 1;
  while i < x
    invariant 1 <= i <= x
    invariant forall t :: 0 <= t < i ==> a[t] <= m
    invariant exists j :: 0 <= j < i && a[j] == m
  {
    if a[i] > m {
      m := a[i];
    }
    i := i + 1;
  }
  p := a.Length - 1;
}
// </vc-code>

