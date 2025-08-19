//ATOM
/* code modified by LLM (iteration 1): Removed unnecessary null check - array<int> is non-nullable by default */
predicate sorted (a:array<int>)
 reads a
{
 sorted_between (a, 0, a.Length)
}


//ATOM
/* code modified by LLM (iteration 1): Removed unnecessary null check - array<int> is non-nullable by default */
predicate sorted_between (a:array<int>, from:nat, to:nat)
 reads a
 requires from <= to
 requires to <= a.Length
{
 forall i,j :: from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}


//IMPL bubbleSort
/* code modified by LLM (iteration 1): Removed unnecessary null check - array<int> is non-nullable by default */
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
        /* code modified by LLM (iteration 1): Correct bubble sort invariant - last i elements are sorted and in final position */
        invariant sorted_between(a, n - i, n)
        invariant forall k, m :: 0 <= k <= n - 1 - i && n - i <= m < n ==> a[k] <= a[m]
    {
        var j := 0;
        
        while j < n - 1 - i
            invariant 0 <= j <= n - 1 - i
            invariant multiset(old(a[..])) == multiset(a[..])
            invariant sorted_between(a, n - i, n)
            invariant forall k, m :: 0 <= k <= n - 1 - i && n - i <= m < n ==> a[k] <= a[m]
            /* code modified by LLM (iteration 1): Inner loop invariant - max element in range [0..j] has bubbled to position j */
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