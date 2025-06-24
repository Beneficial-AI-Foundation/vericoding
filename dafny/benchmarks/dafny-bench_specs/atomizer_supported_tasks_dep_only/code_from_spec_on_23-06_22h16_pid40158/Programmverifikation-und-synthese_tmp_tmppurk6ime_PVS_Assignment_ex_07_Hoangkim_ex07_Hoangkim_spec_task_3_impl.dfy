//IMPL Problem01
//a)
method swap(a: array<int>, i: nat, j: nat)
    modifies a
    requires a != null && a.Length > 0 && i < a.Length && j < a.Length
    ensures a[i] == old(a[j])
    ensures a[j] == old(a[i])
{
    var temp := a[i];
    a[i] := a[j];
    a[j] := temp;
}

//IMPL Problem04
//b)
method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
    minIdx := lo;
    var k := lo + 1;
    while k < a.Length
        invariant lo <= minIdx < a.Length
        invariant lo <= k <= a.Length
        invariant forall x :: lo <= x < k ==> a[minIdx] <= a[x]
    {
        if a[k] < a[minIdx] {
            minIdx := k;
        }
        k := k + 1;
    }
}

//Problem02
ghost predicate sorted(a:seq<int>)
{
    forall i | 0 < i < |a| :: a[i-1] <= a[i]     
}

//IMPL selectionSort
method selectionSort(a: array<int>)
    modifies a
    //ensures multiset(a[..]) == multiset(old(a[..]))
    //ensures sorted(a[..])
{
    if a == null || a.Length <= 1 {
        return;
    }
    
    var i := 0;
    while i < a.Length - 1
    {
        var minIdx := FindMin(a, i);
        swap(a, i, minIdx);
        i := i + 1;
    }
}