

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
  // Find the maximum in a[0..x]
  var max := a[0];
  m := max;
  var j := 1;
  while j < x
    invariant 1 <= j <= x
    invariant forall i :: 0 <= i < j ==> a[i] <= max
    invariant exists i :: 0 <= i < j && a[i] == max
    invariant max == m
  {
    if a[j] > max {
      max := a[j];
      m := max;
    }
    j := j + 1;
  }
  
  // Find the first element > max starting from position x
  p := x;
  while p < a.Length - 1 && a[p] <= max
    invariant x <= p <= a.Length - 1
    invariant forall i :: x <= i < p ==> a[i] <= max
    invariant max == m
  {
    p := p + 1;
  }
  
  // At this point, either p == a.Length - 1 or a[p] > max
  // We need to ensure that if a[p] > max, then a[p] > all previous elements
  if p < a.Length - 1 {
    // a[p] > max, and max is max of a[0..x], so a[p] > all a[0..x]
    // Also, we know that all a[x..p] <= max < a[p]
    assert forall i :: 0 <= i < p ==> a[i] < a[p];
  }
}
// </vc-code>

