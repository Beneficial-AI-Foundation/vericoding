//IMPL 
method reverse(a: array<int>)
 modifies a
 ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
{
    /* code modified by LLM (iteration 4): Store original array values to track reversal correctly */
    var original := new int[a.Length];
    var k := 0;
    while k < a.Length
        invariant 0 <= k <= a.Length
        invariant forall j :: 0 <= j < k ==> original[j] == a[j]
    {
        original[k] := a[k];
        k := k + 1;
    }
    
    var left := 0;
    var right := a.Length - 1;
    
    while left < right
        invariant 0 <= left <= right + 1 <= a.Length
        /* code modified by LLM (iteration 4): Updated invariants to use stored original values */
        invariant forall i :: 0 <= i < left ==> a[i] == original[a.Length - 1 - i]
        invariant forall i :: right < i < a.Length ==> a[i] == original[a.Length - 1 - i]
        invariant forall i :: left <= i <= right ==> a[i] == original[i]
    {
        var temp := a[left];
        a[left] := a[right];
        a[right] := temp;
        
        left := left + 1;
        right := right - 1;
    }
}