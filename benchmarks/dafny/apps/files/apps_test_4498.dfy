Given three integer positions a, b, c on a number line and an integer communication range d,
determine if positions a and c can communicate either directly (distance ≤ d) or indirectly
through position b (both a-b and b-c distances ≤ d).

predicate ValidInput(a: int, b: int, c: int, d: int)
{
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100 && 1 <= d <= 100
}

predicate CanCommunicate(a: int, b: int, c: int, d: int)
{
    abs(a - c) <= d || (abs(a - b) <= d && abs(b - c) <= d)
}

function abs(x: int): int
{
    if x >= 0 then x else -x
}

method solve(a: int, b: int, c: int, d: int) returns (result: string)
    requires ValidInput(a, b, c, d)
    ensures result == "Yes" <==> CanCommunicate(a, b, c, d)
    ensures result == "Yes" || result == "No"
{
    var direct := abs(a - c) <= d;
    var indirect := abs(a - b) <= d && abs(b - c) <= d;

    if direct || indirect {
        result := "Yes";
    } else {
        result := "No";
    }
}
