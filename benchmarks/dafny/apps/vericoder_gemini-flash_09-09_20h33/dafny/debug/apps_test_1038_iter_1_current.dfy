predicate ValidInput(a: int, b: int) {
    0 <= a <= b
}

function XorInt(x: int, y: int): int
    requires x >= 0 && y >= 0
    decreases x + y
    ensures XorInt(x, y) >= 0
{
    if x == 0 && y == 0 then 0
    else if x == 0 then y
    else if y == 0 then x
    else
        var bit_x := x % 2;
        var bit_y := y % 2;
        var xor_bit := if bit_x != bit_y then 1 else 0;
        xor_bit + 2 * XorInt(x / 2, y / 2)
}

function XorRange(a: int, b: int): int
    requires 0 <= a <= b
    decreases b - a
    ensures XorRange(a, b) >= 0
{
    if a == b then a
    else XorInt(a, XorRange(a + 1, b))
}

// <vc-helpers>
function XorFromZeroToN(n: int): int
    requires n >= 0
    ensures XorFromZeroToN(n) >= 0
{
    if n % 4 == 0 then n
    else if n % 4 == 1 then 1
    else if n % 4 == 2 then n + 1
    else 0 // n % 4 == 3
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
    requires ValidInput(a, b)
    ensures result == XorRange(a, b)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    if a == 0 {
        result := XorFromZeroToN(b);
    } else {
        result := XorInt(XorFromZeroToN(a - 1), XorFromZeroToN(b));
    }
}
// </vc-code>

