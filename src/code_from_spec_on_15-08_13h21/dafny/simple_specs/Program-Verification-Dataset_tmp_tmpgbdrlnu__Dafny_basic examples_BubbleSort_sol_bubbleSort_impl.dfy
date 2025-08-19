predicate sorted (a:array<int>)
 reads a
{
 sorted_between (a, 0, a.Length)
}


//ATOM
predicate sorted_between (a:array<int>, from:nat, to:nat)
 reads a
 requires from <= to
 requires to <= a.Length
{
 forall i,j :: from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}


//IMPL bubbleSort

method bubbleSort (a: array<int>)
 modifies a
 requires a.Length > 0
 ensures sorted(a)
 ensures multiset(old(a[..])) == multiset(a[..])
{
    var n := a.Length;
    var i := 0;
    
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant multiset(old(a[..])) == multiset(a[..])
        /* code modified by LLM (iteration 1): Changed invariant to express that last i elements are in their final sorted positions */
        invariant forall k, l :: n - i <= k < l < n ==> a[k] <= a[l]
        /* code modified by LLM (iteration 1): Changed invariant to express that elements in positions n-i to n-1 are >= all elements before them */
        invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> a[k] <= a[l]
    {
        var j := 0;
        while j < n - 1 - i
            invariant 0 <= j <= n - 1 - i
            invariant multiset(old(a[..])) == multiset(a[..])
            /* code modified by LLM (iteration 1): Maintain outer loop invariants */
            invariant forall k, l :: n - i <= k < l < n ==> a[k] <= a[l]
            invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> a[k] <= a[l]
            /* code modified by LLM (iteration 1): Fixed inner loop invariant - largest element in 0..j+1 is at position j */
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