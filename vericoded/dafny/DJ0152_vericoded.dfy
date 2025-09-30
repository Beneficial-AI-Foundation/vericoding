// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  result := a.Length - 1;
  while result >= 0 && a[result] != elem
    invariant -1 <= result < a.Length
    invariant forall i :: result < i < a.Length ==> a[i] != elem
    decreases result
  {
    result := result - 1;
  }
}
// </vc-code>
