// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Find(a: array<int>, key: int) returns (result: int)
    ensures
        (result == -1 || (result >= 0 && result < a.Length)) &&
        (result != -1 ==> (a[result] == key && forall i :: 0 <= i < result ==> a[i] != key)) &&
        (result == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != key)
// </vc-spec>
// <vc-code>
{
  result := -1;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result == -1
    invariant forall j :: 0 <= j < i ==> a[j] != key
  {
    if a[i] == key {
      result := i;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
