method Minimum(a: array<int>) returns (m: int) 
    requires a.Length > 0
    ensures exists i :: 0 <= i < a.Length && m == a[i]
    ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
// </vc-spec>
// <vc-code>
{
  m := a[0];
  var i := 1;
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant exists j :: 0 <= j < i && m == a[j]
    invariant forall j :: 0 <= j < i ==> m <= a[j]
  {
    if a[i] < m {
      m := a[i];
    }
    i := i + 1;
  }
}
// </vc-code>