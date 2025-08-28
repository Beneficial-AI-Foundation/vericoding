// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
    ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if a.Length == 0 {
    return true;
  }
  
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == n
  {
    if a[i] != n {
      return false;
    }
    i := i + 1;
  }
  
  return true;
}
// </vc-code>
