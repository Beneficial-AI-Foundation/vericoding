//IMPL 
method findMax(a:array<int>) returns (pos:int, maxVal: int)
 requires a.Length > 0
 requires forall i :: 0 <= i < a.Length ==> a[i] >= 0
 ensures forall i :: 0 <= i < a.Length ==> a[i] <= maxVal
 ensures exists i :: 0 <= i < a.Length && a[i] == maxVal
 ensures 0 <= pos < a.Length
 ensures a[pos] == maxVal
{
    pos := 0;
    maxVal := a[0];
    
    var i := 1;
    while i < a.Length
        invariant 0 <= pos < a.Length
        invariant maxVal == a[pos]
        /* code modified by LLM (iteration 1): fixed invariant to properly handle the range of processed elements */
        invariant forall k :: 0 <= k < i ==> a[k] <= maxVal
        invariant 1 <= i <= a.Length
    {
        if a[i] > maxVal {
            pos := i;
            maxVal := a[i];
        }
        i := i + 1;
    }
}