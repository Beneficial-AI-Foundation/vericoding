//IMPL Invert
/* code modified by LLM (iteration 2): added helper function for bitwise NOT operation */
function BitwiseNot(x: int): int
{
    -x - 1
}

method Invert(a: array<int>) returns (res: array<int>)
requires a.Length >= 0
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == BitwiseNot(a[i])
{
    /* code modified by LLM (iteration 2): implemented method body to create new array and populate with bitwise NOT values */
    res := new int[a.Length];
    
    /* code modified by LLM (iteration 2): added loop to populate result array with BitwiseNot of each element */
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> res[j] == BitwiseNot(a[j])
    {
        res[i] := BitwiseNot(a[i]);
        i := i + 1;
    }
}