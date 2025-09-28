// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a <= b then a else b }
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
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] != key
    decreases a.Length - i
  {
    if a[i] == key {
      result := i;
      return;
    }
    i := i + 1;
  }
  result := -1;
}
// </vc-code>
