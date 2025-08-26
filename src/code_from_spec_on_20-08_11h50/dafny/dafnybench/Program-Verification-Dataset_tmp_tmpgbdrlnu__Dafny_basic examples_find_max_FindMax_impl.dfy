method FindMax(a: array<int>) returns (max: int)
   requires a != null && a.Length > 0;
   ensures 0 <= max < a.Length;
   ensures forall x :: 0 <= x < a.Length ==> a[max] >= a[x];
// </vc-spec>
// <vc-code>
{
  max := 0;
  var i := 1;
  
  while i < a.Length
    invariant 0 <= max < a.Length;
    invariant 1 <= i <= a.Length;
    invariant forall x :: 0 <= x < i ==> a[max] >= a[x];
  {
    if a[i] > a[max] {
      max := i;
    }
    i := i + 1;
  }
}
// </vc-code>