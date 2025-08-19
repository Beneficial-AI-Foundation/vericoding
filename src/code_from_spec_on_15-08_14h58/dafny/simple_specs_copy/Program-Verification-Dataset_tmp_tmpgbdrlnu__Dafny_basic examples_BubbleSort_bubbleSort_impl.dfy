predicate sorted(a:array<int>, from:int, to:int)
reads a
requires 0 <= from <= to <= a.Length
{
 forall u, v :: from <= u < v < to ==> a[u] <= a[v]
}

//IMPL 
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
        /* code modified by LLM (iteration 2): Fixed invariant to correctly state that the last i elements are sorted */
        invariant forall u, v :: n - i <= u < v < n ==> a[u] <= a[v]
        /* code modified by LLM (iteration 2): Fixed invariant to state that elements before n-i are <= elements after n-i */
        invariant forall u, v :: 0 <= u < n - i && n - i <= v < n ==> a[u] <= a[v]
    {
        var j := 0;
        
        while j < n - 1 - i
            invariant 0 <= j <= n - 1 - i
            invariant multiset(a[..]) == multiset(old(a[..]))
            /* code modified by LLM (iteration 2): Maintain outer loop invariants in inner loop */
            invariant forall u, v :: n - i <= u < v < n ==> a[u] <= a[v]
            invariant forall u, v :: 0 <= u < n - i && n - i <= v < n ==> a[u] <= a[v]
            /* code modified by LLM (iteration 2): Fixed invariant with proper bounds check and bubble property */
            invariant j < n - i - 1 ==> forall k :: 0 <= k <= j ==> a[k] <= a[j + 1]
            /* code modified by LLM (iteration 2): Added invariant that max element in 0..j+1 bubbles to position j+1 */
            invariant forall k :: 0 <= k <= j && j + 1 < n ==> a[k] <= a[j + 1]
        {
            /* code modified by LLM (iteration 2): Added assertion to help prove the swap maintains invariants */
            assert j + 1 < n - i;
            if a[j] > a[j + 1] {
                a[j], a[j + 1] := a[j + 1], a[j];
            }
            j := j + 1;
        }
        /* code modified by LLM (iteration 2): Added assertion to help prove outer invariant maintenance */
        assert j == n - 1 - i;
        assert forall k :: 0 <= k < n - i - 1 ==> a[k] <= a[n - i - 1];
        i := i + 1;
    }
}