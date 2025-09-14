ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
    decreases hi
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
}

// <vc-helpers>
function CountArray(hi: nat, arr: array<int>): nat
    requires 0 <= hi <= arr.Length
    reads arr
    decreases hi
{
    if hi == 0 then 0
    else if arr[hi - 1] % 2 == 0 then 1 + CountArray(hi - 1, arr) else CountArray(hi - 1, arr)
}
// </vc-helpers>

// <vc-spec>
method ComputeCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    decreases CountIndex
    modifies b
    ensures p == Count(CountIndex,a)
// </vc-spec>
// <vc-code>
{
    if CountIndex == 0 {
        return 0;
    } else {
        var prev_p := ComputeCount(CountIndex - 1, a, b);
        if a[CountIndex - 1] % 2 == 0 {
            return prev_p + 1;
        } else {
            return prev_p;
        }
    }
}
// </vc-code>

