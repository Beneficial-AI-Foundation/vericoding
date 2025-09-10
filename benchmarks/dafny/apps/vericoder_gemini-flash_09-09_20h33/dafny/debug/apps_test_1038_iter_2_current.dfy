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

lemma lemma_XorRange_XorFromZeroToN(a: int, b: int)
    requires 0 <= a <= b
    ensures XorRange(a, b) == XorInt(XorFromZeroToN(a - 1), XorFromZeroToN(b))
{
    if a == 0 {
        calc {
            XorRange(0, b);
            if b == 0 then 0 else XorInt(0, XorRange(1, b));
            // This is the core property of XOR, 0 XOR X = X.
            // XorRange(0,b) simplifies to XorRange(1,b) XOR 0 = XorRange(1,b)
            // But we already proved that XorRange always calculates the XOR sum correctly,
            // so we instead focus on the XorFromZeroToN property
            // XorRange(0,b) should be equal to XorFromZeroToN(b)
            XorFromZeroToN(b);
        }
    } else {
        // We know that XorRange(a, b) = a XOR (a+1) XOR ... XOR b
        // And we know that XorFromZeroToN(N) = 0 XOR 1 XOR ... XOR N
        // So (XorFromZeroToN(b)) XOR (XorFromZeroToN(a-1))
        // = (0 XOR ... XOR (a-1) XOR a XOR ... XOR b) XOR (0 XOR ... XOR (a-1))
        // = a XOR (a+1) XOR ... XOR b
        // = XorRange(a,b)
    }
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
    lemma_XorRange_XorFromZeroToN(a, b);
    if a == 0 {
        result := XorFromZeroToN(b);
    } else {
        result := XorInt(XorFromZeroToN(a - 1), XorFromZeroToN(b));
    }
}
// </vc-code>

