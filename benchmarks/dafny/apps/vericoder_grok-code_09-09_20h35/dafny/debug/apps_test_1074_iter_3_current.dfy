function CountOnesInOctal(a: int): int
    requires a >= 0
{
    if a == 0 then 0
    else (if a % 8 == 1 then 1 else 0) + CountOnesInOctal(a / 8)
}

// <vc-helpers>
function CountOnesInOctal(a: int): int
    requires a >= 0
    decreases a
{
    if a == 0 then 0
    else (if a % 8 == 1 then 1 else 0) + CountOnesInOctal(a / 8)
}
// </vc-helpers>

// <vc-spec>
method solve(a: int) returns (count: int)
    requires a >= 0
    ensures count >= 0
    ensures count == CountOnesInOctal(a)
// </vc-spec>
// <vc-code>
decreases a
{
    if a == 0 {
        return 0;
    } else {
        var temp := if a % 8 == 1 then 1 else 0;
        var rec := solve(a / 8);
        return temp + rec;
    }
}
// </vc-code>

