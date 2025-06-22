//IMPL BitwiseXor
/* code modified by LLM (iteration 1): Added helper function for bitwise XOR on natural numbers with proper termination */
function BitwiseXorNat(x: nat, y: nat): int
    decreases x + y
{
    if x == 0 then y
    else if y == 0 then x
    else if x % 2 == y % 2 then 2 * BitwiseXorNat(x / 2, y / 2)
    else 1 + 2 * BitwiseXorNat(x / 2, y / 2)
}

/* code modified by LLM (iteration 1): Added helper function for bitwise XOR operation */
function BitwiseXorInt(x: int, y: int): int
{
    // Bitwise XOR implementation using mathematical operations
    if x >= 0 && y >= 0 then
        BitwiseXorNat(x, y)
    else if x < 0 && y >= 0 then
        -BitwiseXorNat(-x-1, y) - 1
    else if x >= 0 && y < 0 then
        -BitwiseXorNat(x, -y-1) - 1
    else
        BitwiseXorNat(-x-1, -y-1)
}

method BitwiseXor(a: array<int>, b: array<int>) returns (res: array<int>)
requires a.Length == b.Length
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == BitwiseXorInt(a[i], b[i])
{
    res := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant res.Length == a.Length
        /* code modified by LLM (iteration 1): Updated loop invariant to use BitwiseXorInt function */
        invariant forall j :: 0 <= j < i ==> res[j] == BitwiseXorInt(a[j], b[j])
    {
        /* code modified by LLM (iteration 1): Updated assignment to use BitwiseXorInt function */
        res[i] := BitwiseXorInt(a[i], b[i]);
        i := i + 1;
    }
}