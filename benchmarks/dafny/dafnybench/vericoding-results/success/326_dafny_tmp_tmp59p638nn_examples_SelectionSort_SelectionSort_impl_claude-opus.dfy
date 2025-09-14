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

// <vc-helpers>
method FindMin(a: array<int>, start: nat) returns (minIndex: nat)
    requires start < a.Length
    ensures start <= minIndex < a.Length
    ensures forall k :: start <= k < a.Length ==> a[minIndex] <= a[k]
{
    minIndex := start;
    var i := start + 1;
    while i < a.Length
        invariant start < i <= a.Length
        invariant start <= minIndex < i
        invariant forall k :: start <= k < i ==> a[minIndex] <= a[k]
    {
        if a[i] < a[minIndex] {
            minIndex := i;
        }
        i := i + 1;
    }
}

lemma SwapPreservesMultiset(a: array<int>, i: nat, j: nat, old_a: seq<int>)
    requires i < a.Length && j < a.Length
    requires |old_a| == a.Length
    requires i < |old_a| && j < |old_a|
    requires a[..] == old_a[i := old_a[j]][j := old_a[i]]
    ensures multiset(a[..]) == multiset(old_a)
{
    var after := a[..];
    if i == j {
        assert after == old_a;
    } else {
        assert after[i] == old_a[j];
        assert after[j] == old_a[i];
        assert forall k :: 0 <= k < |after| && k != i && k != j ==> after[k] == old_a[k];
    }
}
// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant Ordered(a, 0, i)
        invariant forall x, y :: 0 <= x < i <= y < a.Length ==> a[x] <= a[y]
        invariant Preserved(a, 0, a.Length)
    {
        if i < a.Length - 1 {
            var minIdx := FindMin(a, i);
            if minIdx != i {
                ghost var old_a := a[..];
                var temp := a[i];
                a[i] := a[minIdx];
                a[minIdx] := temp;
                assert a[..] == old_a[i := old_a[minIdx]][minIdx := old_a[i]];
                SwapPreservesMultiset(a, i, minIdx, old_a);
            }
        }
        i := i + 1;
    }
}
// </vc-code>

