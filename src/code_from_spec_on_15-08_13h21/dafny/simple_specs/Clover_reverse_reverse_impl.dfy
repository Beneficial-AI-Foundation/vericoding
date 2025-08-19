//IMPL reverse
method reverse(a: array<int>)
 modifies a
 ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
{
    var left := 0;
    var right := a.Length - 1;
    
    while left < right
        invariant 0 <= left <= right + 1 <= a.Length
        /* code modified by LLM (iteration 2): Fixed invariants to properly track the reversal property */
        invariant forall i :: 0 <= i < left ==> a[i] == old(a[a.Length - 1 - i])
        invariant forall i :: right < i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
        invariant forall i :: left <= i <= right ==> a[i] == old(a[i])
        invariant left + right == a.Length - 1
    {
        /* code modified by LLM (iteration 2): Removed incorrect assertion and added correct ones */
        assert a[left] == old(a[left]);
        assert a[right] == old(a[right]);
        assert left + right == a.Length - 1;
        assert a.Length - 1 - right == left;
        
        var temp := a[left];
        a[left] := a[right];
        a[right] := temp;
        
        left := left + 1;
        right := right - 1;
    }
}