//IMPL
/* code modified by LLM (iteration 1): Added BitwiseNot function definition since it's referenced in the specification but not provided as an atom */
function BitwiseNot(x: int): int
{
    -x - 1
}

/* code modified by LLM (iteration 1): Implemented method with proper loop invariants to satisfy the specification */
method Invert(a: array<int>) returns (res: array<int>)
requires a.Length >= 0
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == BitwiseNot(a[i])
{
    res := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> res[j] == BitwiseNot(a[j])
    {
        res[i] := BitwiseNot(a[i]);
        i := i + 1;
    }
}