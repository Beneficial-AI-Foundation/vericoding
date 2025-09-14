

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
  var maxVal := a[0];
  var i := 1;
  while i < x
      invariant 1 <= i <= x
      invariant forall j :: 0 <= j < i ==> a[j] <= maxVal
      invariant exists j :: 0 <= j < i && a[j] == maxVal
  {
      if a[i] > maxVal {
          maxVal := a[i];
      }
      i := i + 1;
  }
  m := maxVal;

  p := x;
  while p < a.Length && a[p] <= maxVal
      invariant x <= p <= a.Length
      invariant forall j :: x <= j < p ==> a[j] <= maxVal
  {
      p := p + 1;
  }

  if p == a.Length {
      p := a.Length - 1;
  }

  return m, p;
}
// </vc-code>

