//IMPL Power
/* code modified by LLM (iteration 1): Added Pow function to compute integer exponentiation */
function Pow(base: int, exp: nat): int
{
    if exp == 0 then 1
    else base * Pow(base, exp - 1)
}

/* code modified by LLM (iteration 1): Implemented Power method with array allocation and loop */
method Power(a: array<int>, b: array<nat>) returns (res: array<int>)
requires a.Length == b.Length
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == Pow(a[i], b[i])
{
    res := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> res[j] == Pow(a[j], b[j])
    {
        res[i] := Pow(a[i], b[i]);
        i := i + 1;
    }
}