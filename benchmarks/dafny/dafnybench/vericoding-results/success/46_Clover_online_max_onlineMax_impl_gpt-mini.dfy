

// <vc-helpers>
// No helper code needed.
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
  var mm := a[0];
  var i := 1;
  while i < x
    invariant 0 <= i <= x
    invariant forall j :: 0 <= j < i ==> a[j] <= mm
    invariant exists j :: 0 <= j < i && a[j] == mm
    decreases x - i
  {
    if a[i] > mm {
      mm := a[i];
    }
    i := i + 1;
  }

  var pLocal := x;
  while pLocal < a.Length - 1 && a[pLocal] <= mm
    invariant x <= pLocal <= a.Length - 1
    invariant forall j :: 0 <= j < pLocal ==> a[j] <= mm
    decreases a.Length - 1 - pLocal
  {
    pLocal := pLocal + 1;
  }

  p := pLocal;
  m := mm;
}
// </vc-code>

