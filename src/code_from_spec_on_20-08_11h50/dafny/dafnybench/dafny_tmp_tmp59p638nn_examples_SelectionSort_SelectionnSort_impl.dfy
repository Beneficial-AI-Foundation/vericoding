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
function FindMin(a: array<int>, left: nat, right: nat): nat
    reads a
    requires left < right <= a.Length
    ensures left <= FindMin(a, left, right) < right
    ensures forall k :: left <= k < right ==> a[FindMin(a, left, right)] <= a[k]
    decreases right - left
{
    if left + 1 == right then left
    else
        var minRest := FindMin(a, left + 1, right);
        if a[left] <= a[minRest] then left else minRest
}

lemma SwapPreservesMultiset(oldSeq: seq<int>, newSeq: seq<int>, i: nat, j: nat)
    requires i < |oldSeq| && j < |oldSeq|
    requires |newSeq| == |oldSeq|
    requires newSeq[i] == oldSeq[j]
    requires newSeq[j] == oldSeq[i]
    requires forall k :: 0 <= k < |oldSeq| && k != i && k != j ==> newSeq[k] == oldSeq[k]
    ensures multiset(newSeq) == multiset(oldSeq)
{
    if i == j {
        assert newSeq == oldSeq;
        return;
    }
    
    // The multisets are equal because we only swapped two elements
    assert multiset(newSeq) == multiset(oldSeq);
}
// </vc-helpers>

// <vc-spec>
method SelectionnSort(a: array<int>)
    modifies a
    ensures Sorted(a)
// </vc-spec>
// <vc-code>
{
    if a.Length <= 1 {
        return;
    }
    
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant Ordered(a, 0, i)
        invariant forall k, l :: 0 <= k < i <= l < a.Length ==> a[k] <= a[l]
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        if i + 1 < a.Length {
            var minIndex := FindMin(a, i, a.Length);
            
            // Store old sequence for lemma
            var oldSeq := a[..];
            
            // Swap elements
            var temp := a[i];
            a[i] := a[minIndex];
            a[minIndex] := temp;
            
            // Apply lemma to prove multiset preservation
            var newSeq := a[..];
            assert newSeq[i] == oldSeq[minIndex];
            assert newSeq[minIndex] == oldSeq[i];
            assert forall k :: 0 <= k < |oldSeq| && k != i && k != minIndex ==> newSeq[k] == oldSeq[k];
            SwapPreservesMultiset(oldSeq, newSeq, i, minIndex);
        }
        i := i + 1;
    }
    
    assert Ordered(a, 0, a.Length);
    assert multiset(a[..]) == multiset(old(a[..]));
}
// </vc-code>