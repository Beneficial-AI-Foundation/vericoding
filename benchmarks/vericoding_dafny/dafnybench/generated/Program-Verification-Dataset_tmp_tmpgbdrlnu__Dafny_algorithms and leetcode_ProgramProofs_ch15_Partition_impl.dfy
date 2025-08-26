predicate SplitPoint(a: array<int>, n: int)
    reads a
    requires 0 <= n <= a.Length
{
    forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

twostate predicate SwapFrame(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
    (forall i :: 0 <= i < lo || hi <= i < a.Length ==> a[i] == old(a[i])) && multiset(a[..]) == old(multiset(a[..]))
}

// <vc-helpers>
lemma MultisetSwapPreservation(a: array<int>, i: int, j: int)
    requires 0 <= i < a.Length && 0 <= j < a.Length
    ensures multiset(a[..i]) + multiset([a[i]]) + multiset(a[i+1..j]) + multiset([a[j]]) + multiset(a[j+1..]) 
         == multiset(a[..i]) + multiset([a[j]]) + multiset(a[i+1..j]) + multiset([a[i]]) + multiset(a[j+1..])

lemma SplitPointPreservation(a: array<int>, lo: int, hi: int, i: int, j: int)
    requires 0 <= lo <= hi <= a.Length
    requires lo <= i < hi && lo <= j < hi
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    ensures var a' := a[i := a[j]][j := a[i]]; SplitPoint(a', lo) && SplitPoint(a', hi);

lemma MultisetSlicePreservation(a: array<int>, lo: int, hi: int, i: int, j: int)
    requires 0 <= lo <= hi <= a.Length
    requires lo <= i < hi && lo <= j < hi
    ensures var a' := a[i := a[j]][j := a[i]]; multiset(a'[lo..hi]) == multiset(a[lo..hi]);
// </vc-helpers>

// <vc-spec>
method Partition(a: array<int>, lo: int, hi: int) returns (p: int)
    requires 0 <= lo < hi <= a.Length
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures lo <= p < hi
    ensures forall i :: lo <= i < p ==> a[i] < a[p]
    ensures forall i :: p <= i < hi ==> a[p] <= a[i]
    ensures SplitPoint(a, lo) && SplitPoint(a, hi)
    ensures SwapFrame(a, lo, hi)
// </vc-spec>
// <vc-code>
{
    var pivot := a[hi - 1];
    var i := lo;
    var j := lo;
    
    while j < hi - 1
        invariant lo <= i <= j <= hi - 1
        invariant forall k :: lo <= k < i ==> a[k] < pivot
        invariant forall k :: i <= k < j ==> a[k] >= pivot
        invariant a[hi - 1] == pivot
        invariant forall k :: 0 <= k < lo || hi <= k < a.Length ==> a[k] == old(a[k])
        invariant multiset(a[lo..hi]) == old(multiset(a[lo..hi]))
        invariant SplitPoint(a, lo) && SplitPoint(a, hi)
        decreases hi - 1 - j
    {
        if a[j] < pivot {
            if i != j {
                SplitPointPreservation(a, lo, hi, i, j);
                MultisetSlicePreservation(a, lo, hi, i, j);
            }
            a[i], a[j] := a[j], a[i];
            i := i + 1;
        }
        j := j + 1;
    }
    
    if i != hi - 1 {
        SplitPointPreservation(a, lo, hi, i, hi - 1);
        MultisetSlicePreservation(a, lo, hi, i, hi - 1);
    }
    a[i], a[hi - 1] := a[hi - 1], a[i];
    p := i;
}
// </vc-code>