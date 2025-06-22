//IMPL
/* code modified by LLM (iteration 2): Moved BitwiseNot function definition outside method to fix compilation error */
function BitwiseNot(x: int): int
{
    -x - 1
}

method Invert(a: array<int>) returns (res: array<int>)
requires a.Length >= 0
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == BitwiseNot(a[i])
{
    /* code modified by LLM (iteration 2): Fixed method implementation with proper loop invariants */
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