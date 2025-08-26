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
lemma PreservedTransitive(a: array<int>, left: nat, right: nat, oldSeq: seq<int>)
    requires left <= right <= a.Length
    requires |oldSeq| == right - left
    requires multiset(a[left..right]) == multiset(oldSeq)
    ensures multiset(a[left..right]) == multiset(oldSeq)
{
}

lemma MultisetPreservedAfterSwap(a: array<int>, i: int, j: int, oldArray: seq<int>)
    requires 0 <= i < a.Length
    requires 0 <= j < a.Length
    requires |oldArray| == a.Length
    ensures multiset(a[0..a.Length]) == multiset(oldArray[i := oldArray[j]][j := oldArray[i]])
{
}

lemma SwapPreservesMultiset(s: seq<int>, i: int, j: int)
    requires 0 <= i < |s|
    requires 0 <= j < |s|
    ensures multiset(s) == multiset(s[i := s[j]][j := s[i]])
{
}
// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
// </vc-spec>
// <vc-code>
{
    var n := a.Length;
    var i := 0;
    ghost var originalArray := a[0..n];
    
    while i < n
        invariant 0 <= i <= n
        invariant Ordered(a, 0, i)
        invariant multiset(a[0..n]) == multiset(originalArray)
        invariant forall x :: 0 <= x < i ==> forall y :: i <= y < n ==> a[x] <= a[y]
    {
        var minIndex := i;
        var j := i + 1;
        
        while j < n
            invariant i < j <= n
            invariant i <= minIndex < j
            invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
            invariant multiset(a[0..n]) == multiset(originalArray)
        {
            if a[j] < a[minIndex] {
                minIndex := j;
            }
            j := j + 1;
        }
        
        // Swap a[i] and a[minIndex]
        if i != minIndex {
            ghost var beforeSwap := a[0..n];
            var temp := a[i];
            a[i] := a[minIndex];
            a[minIndex] := temp;
            SwapPreservesMultiset(beforeSwap, i, minIndex);
        }
        
        i := i + 1;
    }
    
    assert Ordered(a, 0, a.Length);
    assert multiset(a[0..n]) == multiset(originalArray);
}
// </vc-code>