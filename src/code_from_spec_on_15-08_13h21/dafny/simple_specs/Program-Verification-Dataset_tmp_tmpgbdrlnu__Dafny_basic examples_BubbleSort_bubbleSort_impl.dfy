predicate sorted(a:array<int>, from:int, to:int)
 reads a
 requires 0 <= from <= to <= a.Length
{
 forall u, v :: from <= u < v < to ==> a[u] <= a[v]
}

//IMPL 
/* code modified by LLM (iteration 1): removed redundant null check since array<int> is non-null by default */
method bubbleSort (a: array<int>)
 requires a.Length > 0
 modifies a
 ensures sorted(a, 0, a.Length)
 ensures multiset(a[..]) == multiset(old(a[..]))
{
    var n := a.Length;
    var i := 0;
    
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant multiset(a[..]) == multiset(old(a[..]))
        invariant sorted(a, n - i, n)
        invariant forall u, v :: n - i <= u < n && 0 <= v < n - i ==> a[v] <= a[u]
    {
        var j := 0;
        while j < n - i - 1
            invariant 0 <= j <= n - i - 1
            invariant multiset(a[..]) == multiset(old(a[..]))
            invariant sorted(a, n - i, n)
            invariant forall u, v :: n - i <= u < n && 0 <= v < n - i ==> a[v] <= a[u]
            invariant forall k :: 0 <= k <= j ==> a[k] <= a[j]
        {
            if a[j] > a[j + 1] {
                var temp := a[j];
                a[j] := a[j + 1];
                a[j + 1] := temp;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}