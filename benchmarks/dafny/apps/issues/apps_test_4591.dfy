// <vc-preamble>
predicate ValidInput(a: int, b: int, c: int, x: int, y: int)
{
    1 <= a <= 5000 && 1 <= b <= 5000 && 1 <= c <= 5000 &&
    1 <= x <= 100000 && 1 <= y <= 100000
}

function DirectCost(a: int, b: int, x: int, y: int): int
{
    a * x + b * y
}

function ABOnlyCost(c: int, x: int, y: int): int
{
    2 * c * (if x > y then x else y)
}

function MixedCost(a: int, b: int, c: int, x: int, y: int): int
{
    var max_req := if x > y then x else y;
    var min_req := if x > y then y else x;
    if x > y then
        (x - min_req) * a + 2 * c * min_req
    else
        (y - min_req) * b + 2 * c * min_req
}

function MinCost(a: int, b: int, c: int, x: int, y: int): int
    requires ValidInput(a, b, c, x, y)
{
    if (a + b) <= 2 * c then
        DirectCost(a, b, x, y)
    else
        var ab_cost := ABOnlyCost(c, x, y);
        var mixed_cost := MixedCost(a, b, c, x, y);
        if ab_cost < mixed_cost then ab_cost else mixed_cost
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, x: int, y: int) returns (result: int)
    requires ValidInput(a, b, c, x, y)
    ensures result >= 0
    ensures result == MinCost(a, b, c, x, y)
// </vc-spec>
// <vc-code>
{
    if (a + b) <= 2 * c {
        result := a * x + b * y;
    } else {
        var max_c := if x > y then x else y;
        var min_c := if x > y then y else x;
        var AB := 2 * c * max_c;
        var SP: int;
        if x > y {
            SP := (x - min_c) * a + 2 * c * min_c;
        } else {
            SP := (y - min_c) * b + 2 * c * min_c;
        }
        result := if AB < SP then AB else SP;
    }
}
// </vc-code>
