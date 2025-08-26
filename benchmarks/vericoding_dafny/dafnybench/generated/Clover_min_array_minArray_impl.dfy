method minArray(a: array<int>) returns (r:int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> r <= a[i]
  ensures exists i :: 0 <= i < a.Length && r == a[i]
// </vc-spec>
// <vc-code>
{
  r := a[0];
  var j := 0;
  
  while j < a.Length
    invariant 0 <= j <= a.Length
    invariant forall i :: 0 <= i < j ==> r <= a[i]
    invariant exists i :: 0 <= i < a.Length && r == a[i]
  {
    if a[j] < r {
      r := a[j];
    }
    j := j + 1;
  }
}
// </vc-code>