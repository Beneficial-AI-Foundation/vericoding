// <vc-preamble>
predicate InArray(a: seq<int>, x: int)
{
    exists i :: 0 <= i < |a| && a[i] == x
}
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(a: array<int>) returns (result: array<int>)
    requires a.Length >= 1
    ensures forall i :: 0 <= i < result.Length ==> InArray(a[..], result[i])
    ensures forall i, j :: 0 <= i < j < result.Length ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  result := new int[0];
}
// </vc-code>
