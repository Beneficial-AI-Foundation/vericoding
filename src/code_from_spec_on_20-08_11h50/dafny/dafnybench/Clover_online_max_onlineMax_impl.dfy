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
  // Find the maximum in a[0..x)
  var max_val := a[0];  // Non-ghost copy of the maximum;
  var i := 1;
  while i < x
    invariant 1 <= i <= x
    invariant forall j :: 0 <= j < i ==> a[j] <= max_val
    invariant exists j :: 0 <= j < i && a[j] == max_val
  {
    if a[i] > max_val {
      max_val := a[i];
    }
    i := i + 1;
  }
  
  // Set ghost variable m
  m := max_val;
  
  // Find the first position p >= x where a[p] > max_val
  p := x;
  while p < a.Length && a[p] <= max_val
    invariant x <= p <= a.Length
    invariant forall j :: x <= j < p ==> a[j] <= max_val
    invariant max_val == m
  {
    p := p + 1;
  }
  
  // If we didn't find any element > max_val, set p to the last index
  if p == a.Length {
    p := a.Length - 1;
  }
}
// </vc-code>