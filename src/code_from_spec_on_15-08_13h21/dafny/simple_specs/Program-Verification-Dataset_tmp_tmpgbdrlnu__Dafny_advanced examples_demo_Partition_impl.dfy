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
            // Move negative number to the front
            var temp := a[i];
            a[i] := a[hi];
            a[hi] := a[lo];
            a[lo] := temp;
            lo := lo + 1;
            hi := hi + 1;
        } else if a[i] == 0 {
            // Move zero to the middle section
            var temp := a[i];
            a[i] := a[hi];
            a[hi] := temp;
            hi := hi + 1;
        }
        // If a[i] > 0, it's already in the correct position
        i := i + 1;
    }
}