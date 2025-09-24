// <vc-preamble>
predicate ValidInput(a: int, b: int, x: int, y: int)
{
    0 <= a <= 100000 && 0 <= b <= 100000 && 0 <= x <= 100000 && 0 <= y <= 100000 &&
    (a, b) != (0, 0) && (x, y) != (0, 0) && (a, b) != (x, y)
}

predicate ValidResult(result: string)
{
    result == "Polycarp" || result == "Vasiliy"
}

function OptimalWinner(a: int, b: int, x: int, y: int): string
    requires ValidInput(a, b, x, y)
{
    if a >= x then
        if b >= y then
            "Vasiliy"
        else
            var z := y - b;
            var t := if x - z > 0 then x - z else 0;
            if a - z <= t then "Polycarp" else "Vasiliy"
    else
        if b <= y then
            "Polycarp"
        else
            var z := x - a;
            var t := if y - z > 0 then y - z else 0;
            if b - z <= t then "Polycarp" else "Vasiliy"
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, x: int, y: int) returns (result: string)
    requires ValidInput(a, b, x, y)
    ensures ValidResult(result)
    ensures result == OptimalWinner(a, b, x, y)
// </vc-spec>
// <vc-code>
{
    if a >= x {
        if b >= y {
            result := "Vasiliy";
        } else {
            var z := y - b;
            var t := if x - z > 0 then x - z else 0;
            if a - z <= t {
                result := "Polycarp";
            } else {
                result := "Vasiliy";
            }
        }
    } else {
        if b <= y {
            result := "Polycarp";
        } else {
            var z := x - a;
            var t := if y - z > 0 then y - z else 0;
            if b - z <= t {
                result := "Polycarp";
            } else {
                result := "Vasiliy";
            }
        }
    }
}
// </vc-code>
