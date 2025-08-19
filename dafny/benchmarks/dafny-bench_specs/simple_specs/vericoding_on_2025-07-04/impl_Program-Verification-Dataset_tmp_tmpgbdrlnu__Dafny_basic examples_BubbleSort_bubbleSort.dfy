//ATOM
predicate sorted(a:array<int>, from:int, to:int)
 requires a != null
 reads a
 requires 0 <= from <= to <= a.Length
{
 forall u, v :: from <= u < v < to ==> a[u] <= a[v]
}

//IMPL 
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
        /* code modified by LLM (iteration 1): Fixed sorted invariant - bubble sort places largest elements at the end */
        invariant sorted(a, n - i, n)
        /* code modified by LLM (iteration 1): Fixed bubble property - elements in sorted suffix are >= all elements in unsorted prefix */
        invariant forall u, v :: 0 <= u < n - i <= v < n ==> a[u] <= a[v]
    {
        var j := 0;
        
        while j < n - 1 - i
            invariant 0 <= j <= n - 1 - i
            invariant multiset(a[..]) == multiset(old(a[..]))
            invariant sorted(a, n - i, n)
            invariant forall u, v :: 0 <= u < n - i <= v < n ==> a[u] <= a[v]
            /* code modified by LLM (iteration 1): Fixed inner loop invariant - maximum element in range 0 to j+1 is at position j */
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