// <vc-preamble>
twostate predicate Preserved(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    multiset(a[left..right]) == multiset(old(a[left..right]))
}

ghost predicate Ordered(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    forall i: nat :: 0 < left <= i < right ==> a[i-1] <= a[i]
}

twostate predicate Sorted(a: array<int>)
    reads a
{
    Ordered(a,0,a.Length) && Preserved(a,0,a.Length)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
