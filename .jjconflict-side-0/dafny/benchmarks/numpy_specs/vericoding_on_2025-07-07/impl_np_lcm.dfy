//IMPL LCM

/* code modified by LLM (iteration 2): Fixed GCD function with proper termination and handling of negative remainders */
function GCDInt(a: int, b: int): int
requires a >= 0 && b >= 0
ensures GCDInt(a, b) >= 0
decreases b
{
    if b == 0 then a
    else GCDInt(b, a % b)
}

/* code modified by LLM (iteration 2): Fixed LCM function with proper division handling */
function LCMInt(a: int, b: int): int
requires a >= 0 && b >= 0
ensures LCMInt(a, b) >= 0
{
    if a == 0 || b == 0 then 0
    else 
        var gcd := GCDInt(a, b);
        if gcd > 0 then (a / gcd) * b else 0
}

/* code modified by LLM (iteration 2): Updated method implementation with corrected helper functions */
method LCM(a: array<int>, b: array<int>) returns (res: array<int>)
requires a.Length == b.Length
requires forall i :: 0 <= i < a.Length ==> a[i] >= 0 && b[i] >= 0
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> LCMInt(a[i], b[i]) == res[i]
{
    res := new int[a.Length];
    var i := 0;
    while i < a.Length
    invariant 0 <= i <= a.Length
    invariant res.Length == a.Length
    invariant forall j :: 0 <= j < i ==> LCMInt(a[j], b[j]) == res[j]
    {
        res[i] := LCMInt(a[i], b[i]);
        i := i + 1;
    }
}