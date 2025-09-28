// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SearchInsert(xs: array<int>, target: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < xs.Length ==> xs[i] < xs[j]
    ensures 0 <= result <= xs.Length
    ensures forall i :: 0 <= i < result ==> xs[i] < target
    ensures result < xs.Length ==> target <= xs[result]
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < xs.Length && xs[i] < target
    invariant 0 <= i <= xs.Length
    invariant forall k :: 0 <= k < i ==> xs[k] < target
  {
    i := i + 1;
  }
  result := i;
}
// </vc-code>
