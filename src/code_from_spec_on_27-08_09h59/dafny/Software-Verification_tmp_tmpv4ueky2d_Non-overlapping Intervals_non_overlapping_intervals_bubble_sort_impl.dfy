// Bubble Sort

// Predicates for Bubble Sort
predicate sorted(a: array2<int>, l: int, u: int)
    reads a
    requires a.Length1 == 2
{
    forall i, j :: 0 <= l <= i <= j <= u < a.Length0 ==> a[i, 1] <= a[j, 1]
}

predicate partitioned(a: array2<int>, i: int)
    reads a
    requires a.Length1 == 2
{
    forall k, k' :: 0 <= k <= i < k' < a.Length0 ==> a[k, 1] <= a[k', 1]
}

// <vc-helpers>
lemma sortedTransitive(a: array2<int>, l: int, m: int, u: int)
    requires a.Length1 == 2
    requires sorted(a, l, m) && sorted(a, m, u)
    requires l <= m <= u
    ensures sorted(a, l, u)
{
    forall i, j | 0 <= l <= i <= j <= u < a.Length0
        ensures a[i, 1] <= a[j, 1]
    {
        if j <= m {
            assert a[i, 1] <= a[j, 1];
        } else if i >= m {
            assert a[i, 1] <= a[j, 1];
        } else {
            assert a[i, 1] <= a[m, 1] <= a[j, 1];
        }
    }
}

lemma swapPreservesSort(a: array2<int>, i: int, j: int, l: int, u: int)
    requires a.Length1 == 2
    requires 0 <= l <= i < j <= u < a.Length0
    requires sorted(a, l, i-1) && sorted(a, j+1, u)
    requires a[i, 1] > a[j, 1]
    ensures sorted(a, l, i-1) && sorted(a, j+1, u)
{
}

lemma partitionedImpliesSorted(a: array2<int>, i: int)
    requires a.Length1 == 2
    requires 0 <= i < a.Length0
    requires partitioned(a, i)
    requires sorted(a, 0, i)
    requires sorted(a, i+1, a.Length0-1)
    ensures sorted(a, 0, a.Length0-1)
{
    forall x, y | 0 <= x <= y < a.Length0
        ensures a[x, 1] <= a[y, 1]
    {
        if y <= i {
            assert a[x, 1] <= a[y, 1];
        } else if x > i {
            assert a[x, 1] <= a[y, 1];
        } else {
            assert a[x, 1] <= a[i, 1] <= a[y, 1];
        }
    }
}

lemma bubbleInnerLoopPreservesSorted(a: array2<int>, start: int, end: int)
    requires a.Length1 == 2
    requires 0 <= start <= end < a.Length0
    requires sorted(a, start, end)
    ensures sorted(a, start, end)
{
}

lemma maxElementBubbledUp(a: array2<int>, start: int, end: int)
    requires a.Length1 == 2
    requires 0 <= start < end < a.Length0
    requires forall k :: start <= k < end ==> a[k, 1] <= a[k + 1, 1]
    ensures forall k :: start <= k < end ==> a[k, 1] <= a[end, 1]
{
    forall k | start <= k < end
        ensures a[k, 1] <= a[end, 1]
    {
        var idx := k;
        while idx < end
            invariant k <= idx <= end
            invariant a[k, 1] <= a[idx, 1]
            decreases end - idx
        {
            assert a[idx, 1] <= a[idx + 1, 1];
            idx := idx + 1;
        }
    }
}

lemma bubbleProperty(a: array2<int>, j: int, n: int, i: int)
    requires a.Length1 == 2
    requires 0 <= j < n - i - 1 < a.Length0
    requires forall k :: 0 <= k <= j ==> a[k, 1] <= a[j + 1, 1]
    ensures forall k :: 0 <= k <= j + 1 ==> forall k' :: j + 1 < k' < n - i ==> a[k, 1] <= a[k', 1]
{
}

lemma bubbleStepPreservesInvariant(a: array2<int>, j: int, n: int, i: int)
    requires a.Length1 == 2
    requires 0 <= j < n - i - 1 < a.Length0
    requires forall k :: 0 <= k <= j ==> forall k' :: j + 1 <= k' < n - i ==> a[k, 1] <= a[k', 1]
    requires a[j, 1] <= a[j + 1, 1]
    ensures forall k :: 0 <= k <= j + 1 ==> forall k' :: j + 2 <= k' < n - i ==> a[k, 1] <= a[k', 1]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method bubble_sort(a: array2<int>)
    modifies a
    requires a.Length1 == 2
    ensures sorted(a, 0, a.Length0 - 1)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if a.Length0 <= 1 {
        return;
    }
    
    var n := a.Length0;
    var i := 0;
    
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant sorted(a, n - i, n - 1)
        invariant forall k :: 0 <= k < n - i ==> forall k' :: n - i <= k' < n ==> a[k, 1] <= a[k', 1]
        modifies a
        decreases n - 1 - i
    {
        var j := 0;
        
        while j < n - i - 1
            invariant 0 <= j <= n - i - 1
            invariant sorted(a, n - i, n - 1)
            invariant forall k :: 0 <= k < n - i ==> forall k' :: n - i <= k' < n ==> a[k, 1] <= a[k', 1]
            invariant forall k :: 0 <= k <= j ==> a[k, 1] <= a[j + 1, 1]
            modifies a
            decreases n - i - 1 - j
        {
            if a[j, 1] > a[j + 1, 1] {
                var temp0 := a[j, 0];
                var temp1 := a[j, 1];
                a[j, 0] := a[j + 1, 0];
                a[j, 1] := a[j + 1, 1];
                a[j + 1, 0] := temp0;
                a[j + 1, 1] := temp1;
            }
            j := j + 1;
        }
        
        assert forall k :: 0 <= k < n - i - 1 ==> a[k, 1] <= a[k + 1, 1];
        maxElementBubbledUp(a, 0, n - i - 1);
        
        i := i + 1;
    }
}
// </vc-code>
