//IMPL reverse
method reverse(a: array<int>)
 modifies a
 ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
{
    var left := 0;
    var right := a.Length - 1;
    
    while left < right
        invariant 0 <= left <= right + 1 <= a.Length
        /* code modified by LLM (iteration 4): simplified invariants to track reversed segments */
        invariant forall i :: 0 <= i < left ==> a[i] == old(a[a.Length - 1 - i])
        invariant forall i :: right < i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
        invariant forall i :: left <= i <= right ==> a[i] == old(a[i])
    {
        a[left], a[right] := a[right], a[left];
        left := left + 1;
        right := right - 1;
    }
}