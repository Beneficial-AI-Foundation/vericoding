predicate SplitPoint(a: array<int>, n: int)
    reads a
    requires 0 <= n <= n

{
    forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

// <vc-helpers>
method FindMin(a: array<int>, start: int) returns (minIndex: int)
    requires 0 <= start < a.Length
    ensures start <= minIndex < a.Length
    ensures forall k :: start <= k < a.Length ==> a[minIndex] <= a[k]
{
    minIndex := start;
    var i := start + 1;
    while i < a.Length
        invariant start <= minIndex < a.Length
        invariant start + 1 <= i <= a.Length
        invariant forall k :: start <= k < i ==> a[minIndex] <= a[k]
    {
        if a[i] < a[minIndex] {
            minIndex := i;
        }
        i := i + 1;
    }
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
    var n := 0;
    while n < a.Length
        invariant 0 <= n <= a.Length
        invariant forall i,j :: 0 <= i < j < n ==> a[i] <= a[j]
        invariant forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
        invariant multiset(a[..]) == old(multiset(a[..]))
    {
        var minIndex := FindMin(a, n);
        
        // Swap elements at positions n and minIndex
        var temp := a[n];
        a[n] := a[minIndex];
        a[minIndex] := temp;
        
        n := n + 1;
    }
}
// </vc-code>

twostate predicate SwapFrame(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
    (forall i :: 0 <= i < lo || hi <= i < a.Length ==> a[i] == old(a[i])) && multiset(a[..]) == old(multiset(a[..]))
}