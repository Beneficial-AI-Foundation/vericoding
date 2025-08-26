//Problem01
//a)

//b)
//Problem04

// <vc-spec>
method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
    var j := lo;
    minIdx := lo;
    while j < a.Length
        invariant lo <= j <= a.Length
        invariant lo <= minIdx < a.Length
        invariant forall k :: lo <= k < j ==> a[k] >= a[minIdx]
        decreases a.Length - j
    {
        if(a[j] < a[minIdx]) { minIdx := j; }
        j := j + 1;
    }
}

//Problem02
ghost predicate sorted(a:seq<int>)
{
    forall i | 0 < i < |a| :: a[i-1] <= a[i]     
}

// <vc-helpers>
// </vc-helpers>

method selectionSort(a: array<int>)
    modifies a
    //ensures multiset(a[..]) == multiset(old(a[..]))
    //ensures sorted(a[..])
// </vc-spec>
// <vc-code>
{
    if a == null || a.Length == 0 {
        return;
    }
    
    var i := 0;
    while i < a.Length - 1
        invariant 0 <= i <= a.Length
        decreases a.Length - i
    {
        var minIdx := FindMin(a, i);
        var temp := a[i];
        a[i] := a[minIdx];
        a[minIdx] := temp;
        i := i + 1;
    }
}
// </vc-code>

//Problem03