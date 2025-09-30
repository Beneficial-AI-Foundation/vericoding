// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Max(a: array<int>) returns (result: int)
    requires a.Length > 0
    ensures exists i :: 0 <= i < a.Length && result == a[i]
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= result
// </vc-spec>
// <vc-code>
{
  result := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant exists j :: 0 <= j < i && result == a[j]
    invariant forall j :: 0 <= j < i ==> a[j] <= result
  {
    if a[i] > result {
      result := a[i];
    }
    i := i + 1;
  }
}
// </vc-code>
