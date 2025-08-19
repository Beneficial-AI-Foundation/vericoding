//IMPL 
method Partition(a: array<int>) returns (lo: int, hi: int)
 modifies a
 ensures 0 <= lo <= hi <= a.Length
 ensures forall x | 0 <= x < lo :: a[x] < 0
 ensures forall x | lo <= x < hi :: a[x] == 0
 ensures forall x | hi <= x < a.Length :: a[x] > 0
{
    lo := 0;
    hi := 0;
    var i := 0;
    
    while i < a.Length
        invariant 0 <= lo <= hi <= i <= a.Length
        invariant forall x | 0 <= x < lo :: a[x] < 0
        invariant forall x | lo <= x < hi :: a[x] == 0
        invariant forall x | hi <= x < i :: a[x] > 0
    {
        if a[i] < 0 {
            /* code modified by LLM (iteration 1): Simplified negative number handling */
            // Move negative number to the front
            // First move element at hi to position i
            a[i], a[hi] := a[hi], a[i];
            // Then move the negative number from hi to lo
            a[hi], a[lo] := a[lo], a[hi];
            lo := lo + 1;
            hi := hi + 1;
            i := i + 1;
        } else if a[i] == 0 {
            /* code modified by LLM (iteration 1): Simplified zero handling */
            // Zero goes to the middle section
            a[i], a[hi] := a[hi], a[i];
            hi := hi + 1;
            i := i + 1;
        } else {
            /* code modified by LLM (iteration 1): Positive number stays in place */
            // Positive number is already in the right place
            i := i + 1;
        }
    }
}