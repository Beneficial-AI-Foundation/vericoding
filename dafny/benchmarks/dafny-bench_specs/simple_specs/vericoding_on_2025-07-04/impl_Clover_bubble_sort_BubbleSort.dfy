//IMPL 
method BubbleSort(a: array<int>)
 modifies a
 ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
 ensures multiset(a[..])==multiset(old(a[..]))
{
    var n := a.Length;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        /* code modified by LLM (iteration 3): Corrected invariants - sorted region is from n-i to end */
        invariant forall x, y :: n - i <= x < y < n ==> a[x] <= a[y]
        invariant forall x, y :: 0 <= x < n - i && n - i <= y < n ==> a[x] <= a[y]
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var j := 0;
        
        while j < n - i - 1
            invariant 0 <= j <= n - i - 1
            /* code modified by LLM (iteration 3): Fixed inner invariants - max element bubbles to position j */
            invariant forall k :: 0 <= k <= j ==> a[k] <= a[j]
            invariant forall x, y :: n - i <= x < y < n ==> a[x] <= a[y]
            invariant forall x, y :: 0 <= x < n - i && n - i <= y < n ==> a[x] <= a[y]
            invariant multiset(a[..]) == multiset(old(a[..]))
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