predicate SplitPoint(a: array<int>, n: int)
    reads a
    requires 0 <= n <= n

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
method SwapElements(a: array<int>, i: int, j: int)
    requires 0 <= i < a.Length && 0 <= j < a.Length
    requires i != j
    modifies a
    ensures a[i] == old(a[j]) && a[j] == old(a[i])
    ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    a[i], a[j] := a[j], a[i];
}
// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>)
    modifies a
    ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j, k :: 0 <= j < k < i ==> a[j] <= a[k]
        invariant SplitPoint(a, i)
        invariant multiset(a[..]) == old(multiset(a[..]))
    {
        if i < a.Length - 1 {
            var minIdx := i;
            var j := i + 1;
            
            while j < a.Length
                invariant i < j <= a.Length
                invariant i <= minIdx < a.Length
                invariant forall k :: i <= k < j ==> a[minIdx] <= a[k]
            {
                if a[j] < a[minIdx] {
                    minIdx := j;
                }
                j := j + 1;
            }
            
            assert forall k :: i <= k < a.Length ==> a[minIdx] <= a[k];
            
            if minIdx != i {
                SwapElements(a, i, minIdx);
                assert SplitPoint(a, i);
                assert forall k :: i < k < a.Length ==> a[i] <= a[k];
            }
        }
        i := i + 1;
    }
}
// </vc-code>

