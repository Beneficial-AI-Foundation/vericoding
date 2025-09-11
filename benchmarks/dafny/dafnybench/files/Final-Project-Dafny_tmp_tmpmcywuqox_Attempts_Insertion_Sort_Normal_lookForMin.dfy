// <vc-preamble>
predicate sorted (a: array<int>)

    reads a
{
    sortedA(a, a.Length)
}

predicate sortedA (a: array<int>, i: int)

    requires 0 <= i <= a.Length
    reads a
{
    forall k :: 0 < k < i ==> a[k-1] <= a[k]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method lookForMin (a: array<int>, i: int) returns (m: int)

    requires 0 <= i < a.Length
    ensures i <= m < a.Length
    ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
