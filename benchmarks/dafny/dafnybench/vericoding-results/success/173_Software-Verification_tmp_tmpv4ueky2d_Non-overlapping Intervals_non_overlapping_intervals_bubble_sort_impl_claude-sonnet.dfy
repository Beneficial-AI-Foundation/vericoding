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
lemma sorted_extension(a: array2<int>, l: int, u: int)
    requires a.Length1 == 2
    requires 0 <= l <= u < a.Length0
    requires sorted(a, l, u)
    requires u + 1 < a.Length0
    requires forall k :: l <= k <= u ==> a[k, 1] <= a[u + 1, 1]
    ensures sorted(a, l, u + 1)
{
}

lemma sorted_after_swap(a: array2<int>, i: int, j: int, l: int, u: int)
    requires a.Length1 == 2
    requires 0 <= l <= i < j <= u < a.Length0
    requires sorted(a, l, u)
    requires a[i, 1] > a[j, 1]
    ensures sorted(a, l, u)
{
}

lemma bubble_pass_maintains_sorted(a: array2<int>, sorted_end: int)
    requires a.Length1 == 2
    requires 0 <= sorted_end < a.Length0
    requires sorted(a, sorted_end, a.Length0 - 1)
    ensures sorted(a, sorted_end, a.Length0 - 1)
{
}
// </vc-helpers>

// <vc-spec>
method bubble_sort(a: array2<int>)
    modifies a
    requires a.Length1 == 2
    ensures sorted(a, 0, a.Length0 - 1)
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
        invariant sorted(a, n - 1 - i, n - 1)
        invariant forall k, k' :: 0 <= k < n - 1 - i < k' < n ==> a[k, 1] <= a[k', 1]
        modifies a
    {
        var j := 0;
        
        while j < n - 1 - i
            invariant 0 <= j <= n - 1 - i
            invariant sorted(a, n - 1 - i, n - 1)
            invariant forall k, k' :: 0 <= k < n - 1 - i < k' < n ==> a[k, 1] <= a[k', 1]
            invariant forall k :: 0 <= k < j ==> a[k, 1] <= a[j, 1]
            modifies a
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
        
        i := i + 1;
    }
}
// </vc-code>

