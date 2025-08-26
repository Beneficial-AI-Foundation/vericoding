method max(a: array<int>) returns (x: int)
  requires a.Length != 0
  ensures 0 <= x < a.Length
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= a[x]
// </vc-spec>
// <vc-code>
{
  x := 0;
  var i := 1;
  
  while i < a.Length
    invariant 0 <= x < a.Length
    invariant 1 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] <= a[x]
  {
    if a[i] > a[x] {
      x := i;
    }
    i := i + 1;
  }
}
// </vc-code>