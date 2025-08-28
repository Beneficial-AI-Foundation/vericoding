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
lemma PreservedTransitive(a: array<int>, left: nat, right: nat, mid: nat)
    requires left <= mid <= right <= a.Length
    ensures multiset(a[left..mid]) == multiset(old(a[left..mid])) && 
            multiset(a[mid..right]) == multiset(old(a[mid..right])) ==>
            multiset(a[left..right]) == multiset(old(a[left..right]))
{
    assert a[left..right] == a[left..mid] + a[mid..right];
    assert old(a[left..right]) == old(a[left..mid]) + old(a[mid..right]);
}

lemma PreservedSwap(a: array<int>, left: nat, right: nat, i: nat, j: nat, oldA: seq<int>)
    requires left <= i < j < right <= a.Length
    requires |oldA| == a.Length
    requires multiset(a[left..right]) == multiset(oldA[left..right])
    ensures multiset(a[left..right]) == multiset(oldA[left..right])
{
}

lemma OrderedExtend(a: array<int>, left: nat, right: nat)
    requires left < right <= a.Length
    requires forall k: nat :: left < k < right-1 ==> a[k-1] <= a[k]
    requires right-1 < a.Length && left < right-1 ==> a[right-2] <= a[right-1]
    ensures forall k: nat :: left < k < right ==> a[k-1] <= a[k]
{
}

lemma MultisetSliceSwap(a: array<int>, i: nat, j: nat, left: nat, right: nat, oldA: seq<int>)
    requires 0 <= left <= i < j < right <= a.Length
    requires |oldA| == a.Length
    requires a[left..right] == a[left..i] + a[i..i+1] + a[i+1..j] + a[j..j+1] + a[j+1..right]
    ensures multiset(a[left..right]) == multiset(a[left..i]) + multiset(a[i..i+1]) + multiset(a[i+1..j]) + multiset(a[j..j+1]) + multiset(a[j+1..right])
{
}

lemma SwapPreservesMultiset(a: array<int>, i: nat, j: nat, oldAi: int, oldAj: int, originalSeq: seq<int>)
    requires 0 <= i < j < a.Length
    requires |originalSeq| == a.Length
    requires a[i] == oldAj && a[j] == oldAi
    requires forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == originalSeq[k]
    requires originalSeq[i] == oldAi && originalSeq[j] == oldAj
    ensures multiset(a[..]) == multiset(originalSeq)
{
    assert a[..] == a[..i] + [a[i]] + a[i+1..j] + [a[j]] + a[j+1..];
    assert originalSeq == originalSeq[..i] + [originalSeq[i]] + originalSeq[i+1..j] + [originalSeq[j]] + originalSeq[j+1..];
    assert a[..i] == originalSeq[..i];
    assert a[i+1..j] == originalSeq[i+1..j];  
    assert a[j+1..] == originalSeq[j+1..];
    assert [a[i]] == [originalSeq[j]];
    assert [a[j]] == [originalSeq[i]];
    assert multiset([a[i]]) == multiset([originalSeq[j]]);
    assert multiset([a[j]]) == multiset([originalSeq[i]]);
    assert multiset([originalSeq[i]]) + multiset([originalSeq[j]]) == multiset([originalSeq[j]]) + multiset([originalSeq[i]]);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    var n := a.Length;
    var i := 0;
    ghost var originalArray := a[..];
    
    while i < n
        invariant 0 <= i <= n
        invariant forall k: nat :: 0 < k <= i ==> a[k-1] <= a[k]
        invariant multiset(a[0..n]) == multiset(old(a[0..n]))
        invariant forall k1, k2 :: 0 <= k1 < i <= k2 < n ==> a[k1] <= a[k2]
    {
        var minIdx := i;
        var j := i + 1;
        
        while j < n
            invariant i <= minIdx < j <= n
            invariant forall k :: i <= k < j ==> a[minIdx] <= a[k]
        {
            if a[j] < a[minIdx] {
                minIdx := j;
            }
            j := j + 1;
        }
        
        if minIdx != i {
            ghost var preSwapSeq := a[..];
            var oldAi := a[i];
            var oldAminIdx := a[minIdx];
            a[i] := oldAminIdx;
            a[minIdx] := oldAi;
            
            SwapPreservesMultiset(a, i, minIdx, oldAi, oldAminIdx, preSwapSeq);
        }
        
        i := i + 1;
    }
    
    assert i == n;
    assert forall k: nat :: 0 < k <= n ==> a[k-1] <= a[k];
    assert multiset(a[0..n]) == multiset(old(a[0..n]));
    assert Ordered(a, 0, n);
    assert Preserved(a, 0, n);
}
// </vc-code>
