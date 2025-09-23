// <vc-preamble>
predicate ValidInput(a: int, b: int, c: int, x: int, y: int, z: int)
{
    0 <= a <= 1000000 && 0 <= b <= 1000000 && 0 <= c <= 1000000 &&
    0 <= x <= 1000000 && 0 <= y <= 1000000 && 0 <= z <= 1000000
}

function SphereDeficit(a: int, b: int, c: int, x: int, y: int, z: int): int
{
    max(0, x - a) + max(0, y - b) + max(0, z - c)
}

function SphereProduction(a: int, b: int, c: int, x: int, y: int, z: int): int
{
    max(0, (a - x) / 2) + max(0, (b - y) / 2) + max(0, (c - z) / 2)
}

predicate CanTransform(a: int, b: int, c: int, x: int, y: int, z: int)
{
    SphereProduction(a, b, c, x, y, z) >= SphereDeficit(a, b, c, x, y, z)
}
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int
{
    if a >= b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, x: int, y: int, z: int) returns (result: string)
    requires ValidInput(a, b, c, x, y, z)
    ensures CanTransform(a, b, c, x, y, z) ==> (result == "Yes")
    ensures !CanTransform(a, b, c, x, y, z) ==> (result == "No")
// </vc-spec>
// <vc-code>
{
    var tmpCall1 := max(0, x - a);
    var tmpCall2 := max(0, y - b);
    var tmpCall3 := max(0, z - c);
    var col := tmpCall1 + tmpCall2 + tmpCall3;
    var sum := max(0, (a - x) / 2) + max(0, (b - y) / 2) + max(0, (c - z) / 2);

    if sum >= col {
        return "Yes";
    } else {
        return "No";
    }
}
// </vc-code>
