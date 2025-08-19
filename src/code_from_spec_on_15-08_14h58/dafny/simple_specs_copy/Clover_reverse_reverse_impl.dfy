//IMPL 
method reverse(a: array<int>)
 modifies a
 ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
{
    var left := 0;
    var right := a.Length - 1;
    
    while left < right
        invariant 0 <= left <= right + 1 <= a.Length
        /* code modified by LLM (iteration 3): Added trigger to avoid warning and maintain left+right relationship */
        invariant forall i :: 0 <= i < left ==> a[i] == old(a[a.Length - 1 - i])
        invariant forall i :: right < i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
        invariant forall i {:trigger a[i]} :: left <= i <= right ==> a[i] == old(a[i])
        invariant left + right == a.Length - 1
    {
        /* code modified by LLM (iteration 3): Simplified assertions since left+right relationship is now maintained */
        var temp := a[left];
        a[left] := a[right];
        a[right] := temp;
        
        /* code modified by LLM (iteration 3): Added assertions to help prove invariant maintenance */
        assert a[left] == old(a[right]) == old(a[a.Length - 1 - left]);
        assert a[right] == old(a[left]) == old(a[a.Length - 1 - right]);
        
        left := left + 1;
        right := right - 1;
    }
}