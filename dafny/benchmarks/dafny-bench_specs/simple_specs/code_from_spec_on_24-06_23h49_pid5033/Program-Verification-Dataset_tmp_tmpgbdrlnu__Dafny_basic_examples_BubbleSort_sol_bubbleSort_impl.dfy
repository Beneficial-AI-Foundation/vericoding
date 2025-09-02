//ATOM

predicate sorted (a:array<int>)
 reads a
 requires a!=null
{
 sorted_between (a, 0, a.Length)
}


//ATOM
predicate sorted_between (a:array<int>, from:nat, to:nat)
 reads a
 requires a != null
 requires from <= to
 requires to <= a.Length
{
 forall i,j :: from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}


//IMPL bubbleSort

method bubbleSort (a: array<int>)
 modifies a
 requires a != null
 requires a.Length > 0
 ensures sorted(a)
 ensures multiset(old(a[..])) == multiset(a[..])
{
    var n := a.Length;
    var i := 0;
    
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant multiset(old(a[..])) == multiset(a[..])
        /* code modified by LLM (iteration 1): The last i elements are in their final sorted positions */
        invariant sorted_between(a, n - i, n)
        /* code modified by LLM (iteration 1): Elements in sorted portion are >= all elements before them */
        invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> a[k] <= a[l]
    {
        var j := 0;
        
        while j < n - 1 - i
            invariant 0 <= j <= n - 1 - i
            invariant multiset(old(a[..])) == multiset(a[..])
            /* code modified by LLM (iteration 1): Maintain outer loop invariants */
            invariant sorted_between(a, n - i, n)
            invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> a[k] <= a[l]
            /* code modified by LLM (iteration 1): The maximum element in range [0, j+1] is at position j+1 */
            invariant forall k :: 0 <= k <= j ==> a[k] <= a[j]
        {
            if a[j] > a[j + 1] {
                /* code modified by LLM (iteration 1): Swap elements to maintain bubble property */
                var temp := a[j];
                a[j] := a[j + 1];
                a[j + 1] := temp;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}