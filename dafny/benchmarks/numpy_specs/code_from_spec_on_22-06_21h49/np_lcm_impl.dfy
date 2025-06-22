//IMPL LCM
function LCMInt(a: int, b: int): int
requires a >= 0 && b >= 0
{
    /* code modified by LLM (iteration 4): Fixed precondition handling and GCD call */
    if a == 0 || b == 0 then 0
    else (a * b) / GCD(a, b)
}

/* code modified by LLM (iteration 4): Added GCD helper function with correct termination proof */
function GCD(a: int, b: int): int
requires a > 0 && b > 0
decreases a + b
{
    if a == b then a
    else if a > b then GCD(a - b, b)
    else GCD(a, b - a)
}

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
        /* code modified by LLM (iteration 4): Direct assignment using LCMInt function */
        res[i] := LCMInt(a[i], b[i]);
        i := i + 1;
    }
}