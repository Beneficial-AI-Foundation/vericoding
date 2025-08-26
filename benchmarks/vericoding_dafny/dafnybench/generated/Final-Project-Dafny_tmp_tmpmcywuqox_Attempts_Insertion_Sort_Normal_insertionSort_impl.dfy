predicate sorted (a: array<int>)

    reads a
{
    sortedA(a, a.Length)
}

predicate sortedA (a: array<int>, i: int)

    requires 0 <= i <= a.Length
    reads a
{
    forall k :: 0 < k < i ==> a[k-1] <= a[k]
}

// <vc-spec>
method lookForMin (a: array<int>, i: int) returns (m: int)

    requires 0 <= i < a.Length
    ensures i <= m < a.Length
    ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
{
    var j := i;
    m := i;
    while(j < a.Length)
        invariant i <= j <= a.Length
        invariant i <= m < a.Length
        invariant forall k :: i <= k < j ==> a[k] >= a[m]
        decreases a.Length - j
    {
        if(a[j] < a[m]) { m := j; }
        j := j + 1;
    }
}

// <vc-helpers>
lemma sortedAExtend(a: array<int>, i: int)
    requires 0 <= i < a.Length
    requires sortedA(a, i+1)
    ensures sortedA(a, i)
{
}

lemma sortedAInsert(a: array<int>, old_a: seq<int>, i: int, key: int, j: int)
    requires 0 <= i < a.Length
    requires 0 <= j <= i
    requires |old_a| == a.Length
    requires sortedSeq(old_a, i)
    requires forall k :: 0 <= k <= j ==> a[k] == old_a[k]
    requires forall k :: j+1 <= k <= i ==> a[k] == old_a[k-1] 
    requires j+1 < a.Length ==> a[j+1] == key
    requires forall k :: 0 <= k <= j ==> old_a[k] <= key
    requires forall k :: j+1 <= k < i ==> key <= old_a[k]
    ensures sortedA(a, i+1)
{
}

predicate sortedSeq(s: seq<int>, i: int)
    requires 0 <= i <= |s|
{
    forall k :: 0 < k < i ==> s[k-1] <= s[k]
}

predicate arrayEqual(a: array<int>, b: array<int>)
    requires a.Length == b.Length
    reads a, b
{
    forall k :: 0 <= k < a.Length ==> a[k] == b[k]
}
// </vc-helpers>

method insertionSort (a: array<int>)

    modifies a
    ensures sorted(a)
// </vc-spec>
// <vc-code>
{
    if a.Length <= 1 { return; }
    
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant sortedA(a, i)
    {
        var key := a[i];
        var j := i - 1;
        
        ghost var old_a := a[..];
        
        while j >= 0 && a[j] > key
            invariant -1 <= j < i
            invariant forall k :: j+1 <= k < i ==> a[k] > key
            invariant forall k :: 0 <= k <= j ==> a[k] == old_a[k]
            invariant forall k :: j+2 <= k <= i ==> a[k] == old_a[k-1]
            invariant sortedA(a, j+1)
            invariant forall k :: j+2 <= k <= i ==> a[k-1] <= a[k]
            invariant sortedSeq(old_a, i)
            decreases j
        {
            a[j+1] := a[j];
            j := j - 1;
        }
        
        a[j+1] := key;
        
        assert 0 <= j+1 <= i;
        assert forall k :: 0 <= k <= j ==> a[k] == old_a[k];
        assert forall k :: j+1 <= k <= i ==> a[k] == old_a[k-1];
        assert forall k :: 0 <= k <= j ==> old_a[k] <= key;
        assert forall k :: j+1 <= k < i ==> key <= old_a[k];
        sortedAInsert(a, old_a, i, key, j);
        
        i := i + 1;
    }
}
// </vc-code>