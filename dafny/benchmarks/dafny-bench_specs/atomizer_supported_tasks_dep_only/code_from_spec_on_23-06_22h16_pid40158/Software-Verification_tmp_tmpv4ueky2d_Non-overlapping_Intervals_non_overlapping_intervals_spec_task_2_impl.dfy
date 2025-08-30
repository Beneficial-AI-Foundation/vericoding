//ATOM non_overlapping_intervals
predicate non_overlapping_intervals(a: array2<int>, l: int, u: int)
    reads a
    requires a.Length1 == 2
{
    forall i, j :: l <= i < j <= u < a.Length0 ==> a[i, 1] < a[j, 0] || a[j, 1] < a[i, 0]
}

//IMPL SPEC 
method bubble_sort(a: array2<int>)
    modifies a
    requires a.Length1 == 2
    ensures sorted(a, 0, a.Length0 - 1)
{
    var n := a.Length0;
    if n <= 1 { return; }
    
    var i := 0;
    while i < n - 1
        invariant 0 <= i <= n - 1
        /* code modified by LLM (iteration 4): Fixed outer loop invariant to track that suffix is sorted */
        invariant sorted(a, n - i, n - 1)
        /* code modified by LLM (iteration 4): Added invariant that elements before sorted suffix are <= elements in sorted suffix */
        invariant forall p, q :: 0 <= p < n - i && n - i <= q < n ==> a[p, 1] <= a[q, 1]
    {
        var j := 0;
        while j < n - i - 1
            invariant 0 <= j <= n - i - 1
            /* code modified by LLM (iteration 4): Maintain outer loop invariants */
            invariant sorted(a, n - i, n - 1)
            invariant forall p, q :: 0 <= p < n - i && n - i <= q < n ==> a[p, 1] <= a[q, 1]
            /* code modified by LLM (iteration 4): Track that maximum element in range [0..j] has bubbled to position j */
            invariant forall k :: 0 <= k <= j ==> a[k, 1] <= a[j, 1]
        {
            if a[j, 1] > a[j + 1, 1] {
                // Swap rows j and j+1
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

//ATOM 
predicate sorted(a: array2<int>, l: int, u: int)
    reads a
    requires a.Length1 == 2
{
    forall i, j :: 0 <= l <= i <= j <= u < a.Length0 ==> a[i, 1] <= a[j, 1]
}

//ATOM partitioned
predicate partitioned(a: array2<int>, pivot: int, l: int, u: int)
    reads a
    requires a.Length1 == 2
{
    forall i, j :: l <= i < pivot < j <= u < a.Length0 ==> a[i, 1] <= a[j, 1]
}