predicate ValidInput(a: int, b: int)
{
    a > 0 && b > 0
}

function countSquares(a: int, b: int): int
    requires a >= 0 && b >= 0
    ensures a > 0 && b > 0 && a > b ==> countSquares(a, b) >= 1
    ensures a > 0 && b > 0 && b > a ==> countSquares(a, b) >= 1
    ensures a > 0 && b > 0 && a == b ==> countSquares(a, b) == 1
    decreases a + b
{
    if a == 0 || b == 0 then 0
    else if a > b then a / b + countSquares(a % b, b)
    else b / a + countSquares(a, b % a)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
    requires ValidInput(a, b)
    ensures result >= 0
    ensures (a == b) ==> (result == 1)
    ensures a > b ==> result >= 1
    ensures result == countSquares(a, b)
// </vc-spec>
// <vc-code>
{
    if a == b {
        result := 1;
    } else if a > b {
        var quotient := a / b;
        var remainder := a % b;
        if remainder == 0 {
            result := quotient;
        } else {
            var subResult := solve(remainder, b);
            result := quotient + subResult;
        }
    } else {
        var quotient := b / a;
        var remainder := b % a;
        if remainder == 0 {
            result := quotient;
        } else {
            var subResult := solve(a, remainder);
            result := quotient + subResult;
        }
    }
}
// </vc-code>

