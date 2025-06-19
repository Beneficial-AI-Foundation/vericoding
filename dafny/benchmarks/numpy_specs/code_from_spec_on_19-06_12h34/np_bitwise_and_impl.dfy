//IMPL
/* code modified by LLM (iteration 2): Added proper helper function outside method for bitwise AND operation */
function BitwiseAndInt(x: int, y: int): int
{
    if x == 0 || y == 0 then 0
    else if x > 0 && y > 0 then 
        2 * BitwiseAndInt(x / 2, y / 2) + (if (x % 2 == 1 && y % 2 == 1) then 1 else 0)
    else if x < 0 && y < 0 then
        // For negative numbers, use two's complement representation
        if x == -1 then y
        else if y == -1 then x  
        else 2 * BitwiseAndInt(x / 2, y / 2) + (if (x % 2 != 0 && y % 2 != 0) then 1 else 0)
    else 
        // One positive, one negative
        if x < 0 then BitwiseAndInt(x, y)
        else BitwiseAndInt(x, y)
}

method BitwiseAnd(a: array<int>, b: array<int>) returns (res: array<int>)
requires a.Length == b.Length
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == BitwiseAndInt(a[i], b[i])
{
    /* code modified by LLM (iteration 2): Fixed method implementation to use correct helper function */
    res := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant res.Length == a.Length
        invariant forall j :: 0 <= j < i ==> res[j] == BitwiseAndInt(a[j], b[j])
    {
        res[i] := BitwiseAndInt(a[i], b[i]);
        i := i + 1;
    }
}