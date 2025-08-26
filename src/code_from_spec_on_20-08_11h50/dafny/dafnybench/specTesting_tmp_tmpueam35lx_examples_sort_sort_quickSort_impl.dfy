method quickSort(intSeq:array<int>)
    modifies intSeq
    ensures forall i:nat, j:nat | 0 <= i <= j < intSeq.Length :: intSeq[i] <= intSeq[j]
    // ensures multiset(intSeq[..]) == multiset(old(intSeq[..]))


lemma sort(prevSeq:seq<int>) returns (curSeq:seq<int>)
    ensures (forall i:nat, j:nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j])
    ensures multiset(prevSeq) == multiset(curSeq)

predicate post_sort(prevSeq:seq<int>, curSeq:seq<int>)
// </vc-spec>
// <vc-code>
{
  (forall i:nat, j:nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j]) &&
  multiset(prevSeq) == multiset(curSeq)
}

method quickSort(intSeq:array<int>)
    modifies intSeq
    ensures forall i:nat, j:nat | 0 <= i <= j < intSeq.Length :: intSeq[i] <= intSeq[j]
{
    quickSortHelper(intSeq, 0, intSeq.Length);
}

method quickSortHelper(intSeq:array<int>, low:nat, high:nat)
    requires 0 <= low <= high <= intSeq.Length
    modifies intSeq
    ensures forall i:nat, j:nat | low <= i <= j < high :: intSeq[i] <= intSeq[j]
    ensures forall i:nat | 0 <= i < low || high <= i < intSeq.Length :: intSeq[i] == old(intSeq[i])
    ensures multiset(intSeq[..]) == multiset(old(intSeq[..]))
    decreases high - low
{
    if low + 1 < high {
        var pivotIndex := partition(intSeq, low, high);
        quickSortHelper(intSeq, low, pivotIndex);
        quickSortHelper(intSeq, pivotIndex + 1, high);
    }
}

method partition(intSeq:array<int>, low:nat, high:nat) returns (pivotIndex:nat)
    requires 0 <= low < high <= intSeq.Length
    modifies intSeq
    ensures low <= pivotIndex < high
    ensures forall i:nat | low <= i <= pivotIndex :: intSeq[i] <= intSeq[pivotIndex]
    ensures forall i:nat | pivotIndex < i < high :: intSeq[pivotIndex] <= intSeq[i]
    ensures forall i:nat | 0 <= i < low || high <= i < intSeq.Length :: intSeq[i] == old(intSeq[i])
    ensures multiset(intSeq[..]) == multiset(old(intSeq[..]))
{
    var pivot := intSeq[high - 1];
    var i := low;
    var j := low;
    
    while j < high - 1
        invariant low <= i <= j <= high - 1
        invariant forall k:nat | low <= k < i :: intSeq[k] <= pivot
        invariant forall k:nat | i <= k < j :: intSeq[k] > pivot
        invariant intSeq[high - 1] == pivot
        invariant forall k:nat | 0 <= k < low || high <= k < intSeq.Length :: intSeq[k] == old(intSeq[k])
        invariant multiset(intSeq[..]) == multiset(old(intSeq[..]))
    {
        if intSeq[j] <= pivot {
            intSeq[i], intSeq[j] := intSeq[j], intSeq[i];
            i := i + 1;
        }
        j := j + 1;
    }
    
    intSeq[i], intSeq[high - 1] := intSeq[high - 1], intSeq[i];
    pivotIndex := i;
}

lemma sort(prevSeq:seq<int>) returns (curSeq:seq<int>)
    ensures (forall i:nat, j:nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j])
    ensures multiset(prevSeq) == multiset(curSeq)
    decreases |prevSeq|
{
    if |prevSeq| == 0 {
        curSeq := [];
    } else if |prevSeq| == 1 {
        curSeq := prevSeq;
    } else {
        var pivot := prevSeq[0];
        var smallerElems := [prevSeq[k] | k in 1..| prevSeq| | prevSeq[k] <= pivot];
        var largerElems := [prevSeq[k] | k in 1..| prevSeq| | prevSeq[k] > pivot];
        
        var sortedSmaller := sort(smallerElems);
        var sortedLarger := sort(largerElems);
        
        curSeq := sortedSmaller + [pivot] + sortedLarger;
    }
}
// </vc-code>
// <vc-helpers>
// </vc-helpers>

lemma multisetAdditivity(m1:multiset<int>, m2:multiset<int>, m3:multiset<int>, m4:multiset<int>)
    requires m1 == m2 + m3
    requires m1 == m2 + m4
    ensures m3 == m4
    {
        assert m3 == m1 - m2;
        assert m4 == m1 - m2;
    }


lemma twoSortedSequencesWithSameElementsAreEqual(s1:seq<int>, s2:seq<int>)
    requires (forall i:nat, j:nat | 0 <= i <= j < |s1| :: s1[i] <= s1[j])
    requires (forall i:nat, j:nat | 0 <= i <= j < |s2| :: s2[i] <= s2[j])
    requires multiset(s1) == multiset(s2)
    requires |s1| == |s2|
    ensures s1 == s2
{
    if (|s1| != 0) {
        if s1[|s1|-1] == s2[|s2|-1] {
        assert multiset(s1[..|s1|-1]) == multiset(s2[..|s2|-1]) by {
            assert s1 == s1[..|s1|-1] + [s1[|s1|-1]];
            assert multiset(s1) == multiset(s1[..|s1|-1]) + multiset([s1[|s1|-1]]);

            assert s2 == s2[..|s1|-1] + [s2[|s1|-1]];
            assert multiset(s2) == multiset(s2[..|s1|-1]) + multiset([s2[|s1|-1]]);

            assert multiset([s1[|s1|-1]]) == multiset([s2[|s1|-1]]);

            multisetAdditivity(multiset(s1), multiset([s1[|s1|-1]]), multiset(s1[..|s1|-1]), multiset(s2[..|s1|-1]));
        }
        twoSortedSequencesWithSameElementsAreEqual(s1[..|s1|-1], s2[..|s2|-1]);
        } else if s1[|s1|-1] < s2[|s2|-1] {
            assert s2[|s2|-1] !in multiset(s1);
            assert false;
        } else {
            assert s1[|s1|-1] !in multiset(s2);
            assert false;
        }
    }
}

lemma sort_determinisitc(prevSeq:seq<int>, curSeq:seq<int>, curSeq':seq<int>)
    requires post_sort(prevSeq, curSeq)
    requires post_sort(prevSeq, curSeq')
    ensures curSeq == curSeq'
{

    if (|curSeq| != |curSeq'|) {
        assert |multiset(curSeq)| != |multiset(curSeq')|;
    } else {
        twoSortedSequencesWithSameElementsAreEqual(curSeq, curSeq');
    }
}

lemma sort_determinisitc1(prevSeq:seq<int>, curSeq:seq<int>, curSeq':seq<int>)
    requires prevSeq == [5,4,3,2,1]
    requires post_sort(prevSeq, curSeq)
    requires post_sort(prevSeq, curSeq')
    ensures curSeq == curSeq'
{
}