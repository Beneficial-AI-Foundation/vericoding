// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min2(x: int, y: int): int {
  if x <= y then x else y
}
// </vc-helpers>

// <vc-spec>
method min(a: array<int>) returns (result: int)
    requires a.Length > 0
    ensures exists i :: 0 <= i < a.Length && result == a[i]
    ensures forall i :: 0 <= i < a.Length ==> result <= a[i]
// </vc-spec>
// <vc-code>
{
  var m := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> m <= a[j]
    invariant exists j :: 0 <= j < i && m == a[j]
    decreases a.Length - i
  {
    if a[i] < m {
      m := a[i];
    }
    i := i + 1;
  }
  result := m;
}
// </vc-code>
