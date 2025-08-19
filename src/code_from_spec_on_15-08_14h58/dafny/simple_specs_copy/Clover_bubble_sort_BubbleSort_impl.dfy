//IMPL BubbleSort
method BubbleSort(a: array<int>)
modifies a
ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
ensures multiset(a[..])==multiset(old(a[..]))
{
    var n := a.Length;
    var i := 0;
    
    /* code modified by LLM (iteration 4): Fixed outer loop invariants with proper bounds checking and correct logic */
    while i < n
        invariant 0 <= i <= n
        invariant multiset(a[..]) == multiset(old(a[..]))
        invariant forall k1, k2 :: n - i <= k1 < k2 < n ==> a[k1] <= a[k2]
        invariant forall k1, k2 :: 0 <= k1 < n - i && n - i <= k2 < n ==> a[k1] <= a[k2]
    {
        var j := 0;
        
        /* code modified by LLM (iteration 4): Fixed inner loop invariants with proper bounds and added trigger */
        while j < n - 1 - i
            invariant 0 <= j <= n - 1 - i
            invariant multiset(a[..]) == multiset(old(a[..]))
            invariant forall k1, k2 :: n - i <= k1 < k2 < n ==> a[k1] <= a[k2]
            invariant forall k1, k2 :: 0 <= k1 < n - i && n - i <= k2 < n ==> a[k1] <= a[k2]
            invariant forall k :: 0 <= k < j ==> (k + 1 < n && a[k] <= a[k + 1])
            invariant forall k :: 0 <= k < j && n - i < n ==> a[k] <= a[n - i - 1]
        {
            /* code modified by LLM (iteration 4): Added bounds check before comparison */
            if j + 1 < n && a[j] > a[j + 1] {
                a[j], a[j + 1] := a[j + 1], a[j];
            }
            j := j + 1;
        }
        i := i + 1;
    }
}