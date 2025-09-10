function CountValidMinutes(a: int, b: int): int
    requires a >= 0 && b >= 0
    decreases a + b
{
    if a <= 0 || b <= 0 then 0
    else if a == 1 && b == 1 then 0
    else (if a > 1 || b > 1 then 1 else 0) + 
         CountValidMinutes(if a < b then a + 1 else a - 2, if a < b then b - 2 else b + 1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(a1: int, a2: int) returns (result: int)
    requires a1 >= 1 && a2 >= 1
    ensures result >= 0
    ensures result == CountValidMinutes(a1, a2)
    ensures (a1 == 1 && a2 == 1) ==> result == 0
// </vc-spec>
// <vc-code>
{
    if a1 <= 0 || a2 <= 0 then
        return 0;
    else if a1 == 1 && a2 == 1 then
        return 0;
    else
        var recursive_result := solve(if a1 < a2 then a1 + 1 else a1 - 2, if a1 < a2 then a2 - 2 else a2 + 1);
        return (if a1 > 1 || a2 > 1 then 1 else 0) + recursive_result;
}
// </vc-code>

