//ATOM
predicate sorted(a:array<int>, from:int, to:int)
 requires a != null
 reads a
 requires 0 <= from <= to <= a.Length
{
 forall u, v :: from <= u < v < to ==> a[u] <= a[v]
}

//IMPL bubbleSort
method bubbleSort (a: array<int>)
 requires a != null && a.Length > 0
 modifies a
 ensures sorted(a, 0, a.Length)
 ensures multiset(a[..]) == multiset(old(a[..]))
{
    var n := a.Length;
    var i := 0;
    
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant multiset(a[..]) == multiset(old(a[..]))
        /* code modified by LLM (iteration 2): The sorted portion grows from right to left - elements from n-i to n are sorted and in final positions */
        invariant sorted(a, n - i, n)
        /* code modified by LLM (iteration 2): Elements in the sorted portion are >= all elements in the unsorted portion */
        invariant forall u, v :: 0 <= u < n - i && n - i <= v < n ==> a[u] <= a[v]
    {
        var j := 0;
        
        while j < n - 1 - i
            invariant 0 <= j <= n - 1 - i
            invariant multiset(a[..]) == multiset(old(a[..]))
            invariant sorted(a, n - i, n)
            invariant forall u, v :: 0 <= u < n - i && n - i <= v < n ==> a[u] <= a[v]
            /* code modified by LLM (iteration 2): The maximum element in range [0, j+1] is at position j */
            invariant forall k :: 0 <= k <= j ==> a[k] <= a[j]
        {
            if a[j] > a[j + 1] {
                a[j], a[j + 1] := a[j + 1], a[j];
            }
            j := j + 1;
        }
        
        i := i + 1;
    }
}