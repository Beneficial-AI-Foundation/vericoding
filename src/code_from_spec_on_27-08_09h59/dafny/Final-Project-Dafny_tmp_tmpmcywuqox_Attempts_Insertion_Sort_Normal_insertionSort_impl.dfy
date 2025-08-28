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

method lookForMin (a: array<int>, i: int) returns (m: int)

    requires 0 <= i < a.Length
    ensures i <= m < a.Length
    ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma sortedAExtend(a: array<int>, i: int)
    requires 0 <= i < a.Length
    requires sortedA(a, i)
    requires i == 0 || a[i-1] <= a[i]
    ensures sortedA(a, i+1)
{
    if i == 0 {
        assert sortedA(a, 1);
    } else {
        forall k | 0 < k < i+1
            ensures a[k-1] <= a[k]
        {
            if k < i {
                assert a[k-1] <= a[k];
            } else {
                assert k == i;
                assert a[i-1] <= a[i];
            }
        }
    }
}

lemma sortedAPreserved(a: array<int>, i: int, j: int, oldVal: int, newVal: int)
    requires 0 <= i <= j < a.Length
    requires sortedA(a, i)
    requires oldVal >= newVal
    requires forall k :: 0 <= k < i ==> a[k] <= newVal
    ensures sortedA(a, i+1)
{
}

lemma shiftPreservesSorted(a: array<int>, pos: int, val: int)
    requires 0 <= pos < a.Length
    requires sortedA(a, pos+1)
    requires pos == 0 || a[pos-1] <= val
    ensures sortedA(a, pos+1)
{
}

lemma insertionMaintainsSorted(a: array<int>, pos: int, key: int)
    requires 0 <= pos <= a.Length
    requires sortedA(a, pos)
    requires pos == 0 || a[pos-1] <= key
    ensures sortedA(a, pos+1)
{
    if pos + 1 <= a.Length {
        forall k | 0 < k < pos + 1
            ensures a[k-1] <= a[k]
        {
            if k < pos {
                assert a[k-1] <= a[k];
            } else {
                assert k == pos;
                if pos > 0 {
                    assert a[pos-1] <= key;
                }
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method insertionSort (a: array<int>)

    modifies a
    ensures sorted(a)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if a.Length <= 1 {
        return;
    }
    
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant sortedA(a, i)
    {
        var key := a[i];
        var j := i - 1;
        
        while j >= 0 && a[j] > key
            invariant -1 <= j < i
            invariant sortedA(a, j+1)
            invariant forall k :: j+1 < k < i ==> a[k] >= key
            invariant forall k :: 0 <= k < j+1 ==> a[k] <= key
            invariant a[i] == key
        {
            a[j+1] := a[j];
            j := j - 1;
        }
        
        a[j+1] := key;
        
        assert -1 <= j < i;
        assert j == -1 || a[j] <= key;
        
        assert sortedA(a, j+1);
        assert j+1 == 0 || a[j] <= key;
        
        if j >= 0 {
            assert a[j] <= key;
            assert a[j] == a[j+1-1];
            assert j+1 > 0;
        }
        
        sortedAExtend(a, i);
        
        i := i + 1;
    }
}
// </vc-code>
