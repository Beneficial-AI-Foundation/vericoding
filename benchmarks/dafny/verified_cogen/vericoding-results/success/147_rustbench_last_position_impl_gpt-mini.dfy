// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method LastPosition(a: array<int>, elem: int) returns (result: int)
    requires 0 < a.Length < 100_000
    requires exists i :: 0 <= i < a.Length && a[i] == elem
    ensures 0 <= result < a.Length
    ensures forall i :: result < i < a.Length ==> a[i] != elem
    ensures a[result] == elem
// </vc-spec>
// <vc-code>
{
  var index := a.Length - 1;
  while index >= 0 && a[index] != elem
    invariant -1 <= index < a.Length
    invariant forall i :: index < i < a.Length ==> a[i] != elem
    invariant exists k :: 0 <= k <= index && a[k] == elem
    decreases index + 1
  {
    index := index - 1;
  }
  assert 0 <= index < a.Length;
  assert a[index] == elem;
  result := index;
}
// </vc-code>
