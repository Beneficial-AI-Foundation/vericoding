predicate ValidInput(a: int, b: int, c: int, d: int)
{
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100 && 1 <= d <= 100
}

predicate CanCommunicate(a: int, b: int, c: int, d: int)
{
    abs(a - c) <= d || (abs(a - b) <= d && abs(b - c) <= d)
}

// <vc-helpers>
function abs(x: int): int
{
    if x < 0 then -x else x
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, d: int) returns (result: string)
    requires ValidInput(a, b, c, d)
    ensures result == "Yes" <==> CanCommunicate(a, b, c, d)
    ensures result == "Yes" || result == "No"
// </vc-spec>
// <vc-code>
{
    if abs(a - c) <= d {
        result := "Yes";
    } else if abs(a - b) <= d && abs(b - c) <= d {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

