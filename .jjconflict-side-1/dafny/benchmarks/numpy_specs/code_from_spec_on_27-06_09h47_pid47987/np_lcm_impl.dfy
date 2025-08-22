//IMPL
method LCM(a: array<int>, b: array<int>) returns (res: array<int>)
requires a.Length == b.Length
requires forall i :: 0 <= i < a.Length ==> a[i] >= 0 && b[i] >= 0
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> LCMInt(a[i], b[i]) == res[i]
{
    res := new int[a.Length];
    
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> LCMInt(a[j], b[j]) == res[j]
    {
        res[i] := LCMInt(a[i], b[i]);
    }
}

/* code modified by LLM (iteration 1): Fixed precondition and division by zero handling */
function LCMInt(x: int, y: int): int
requires x >= 0 && y >= 0
{
    if x == 0 || y == 0 then 0
    else (x * y) / GCDInt(x, y)
}

/* code modified by LLM (iteration 1): Fixed termination and ensured GCD is always positive for positive inputs */
function GCDInt(x: int, y: int): int
requires x > 0 && y > 0
ensures GCDInt(x, y) > 0
decreases if x <= y then y else x
{
    if x == y then x
    else if x < y then GCDInt(x, y - x)
    else GCDInt(x - y, y)
}