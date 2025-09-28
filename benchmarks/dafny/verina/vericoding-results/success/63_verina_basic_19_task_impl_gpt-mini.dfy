// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Sorted(a: seq<int>): bool {
  forall i :: 0 <= i < |a| - 1 ==> a[i] <= a[i + 1]
}
// </vc-helpers>

// <vc-spec>
method IsSorted(a: seq<int>) returns (result: bool)
    ensures
        result == (forall i :: 0 <= i < |a| - 1 ==> a[i] <= a[i + 1])
// </vc-spec>
// <vc-code>
{
  result := Sorted(a);
}
// </vc-code>
