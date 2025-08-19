method InvertArray(a: array<int>)
 modifies a
 ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length-1-i])
{
    var left := 0;
    var right := a.Length - 1;
    
    while left < right
        invariant 0 <= left <= right + 1 <= a.Length
        /* code modified by LLM (iteration 1): Fixed invariants to properly track swapped elements and their correct positions */
        invariant forall i | 0 <= i < left :: a[i] == old(a[a.Length-1-i])
        invariant forall i | right < i < a.Length :: a[i] == old(a[a.Length-1-i])
        invariant forall i | left <= i <= right :: a[i] == old(a[i])
        invariant left + right == a.Length - 1
    {
        /* code modified by LLM (iteration 2): Added assertion to help verification understand the relationship between indices */
        assert left + right == a.Length - 1;
        assert a.Length - 1 - left == right;
        assert a.Length - 1 - right == left;
        
        var temp := a[left];
        a[left] := a[right];
        a[right] := temp;
        
        /* code modified by LLM (iteration 2): Fixed assertions to properly reference array elements instead of using temp as an index */
        assert a[left] == old(a[right]);
        assert a[right] == old(a[left]);
        assert a[left] == old(a[a.Length-1-left]);
        assert a[right] == old(a[a.Length-1-right]);
        
        left := left + 1;
        right := right - 1;
    }
}