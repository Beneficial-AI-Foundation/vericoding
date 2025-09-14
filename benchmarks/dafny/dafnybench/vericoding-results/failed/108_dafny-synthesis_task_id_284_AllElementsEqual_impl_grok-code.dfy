

// <vc-helpers>
method AllElementsEqualHelper(a: array?<int>, n: int) returns (result: bool)
  ensures result ==> forall i : int :: 0 <= i < a.Length ==> a[i] == n
  ensures !result ==> exists i : int :: 0 <= i < a.Length && a[i] != n
  requires a != null
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k : int :: 0 <= k < i ==> a[k] == n
  {
    if a[i] != n {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-helpers>

// <vc-spec>
method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
    ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k : int :: 0 <= k < i ==> a[k] == n
  {
    if a[i] != n {
      result := false;
    }
    i := i + 1;
  }
  result := true;
}
// </vc-code>

