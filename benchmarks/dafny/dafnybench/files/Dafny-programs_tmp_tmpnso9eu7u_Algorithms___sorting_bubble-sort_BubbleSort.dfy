// <vc-preamble>
predicate sorted_between(A:array<int>, from:int, to:int)
    reads A
{
    forall i, j :: 0 <= i <= j < A.Length && from <= i <= j <= to ==> A[i] <= A[j]
}

predicate sorted(A:array<int>)
    reads A
{
    sorted_between(A, 0, A.Length-1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method BubbleSort(A:array<int>)
    modifies A
    ensures sorted(A)
    ensures multiset(A[..]) == multiset(old(A[..]))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
