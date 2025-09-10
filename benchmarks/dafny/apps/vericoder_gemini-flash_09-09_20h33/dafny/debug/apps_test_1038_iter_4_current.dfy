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
    requires n >= -1 // Allow n = -1 for the base case (a=0) in XorRange calculation
    ensures XorFromZeroToN(n) >= 0
{
    if n == -1 then 0 // Define XorFromZeroToN(-1) as 0
    else if n % 4 == 0 then n
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
            // XorRange(0,b) is 0 XOR 1 XOR ... XOR b, which is XorFromZeroToN(b)
            // Proof that XorRange(0, b) == XorFromZeroToN(b)
            // This relies on the definition of XorRange and XorFromZeroToN.
            // XorRange(0,b) = 0 ^ XorRange(1,b)
            // XorRange(1,b) = 1 ^ XorRange(2,b)
            // ...
            // XorRange(b,b) = b
            // So XorRange(0,b) = 0 ^ 1 ^ ... ^ b
            // This is exactly the definition of XorFromZeroToN(b) for n >= 0.
            XorFromZeroToN(b);
            XorInt(XorFromZeroToN(a - 1), XorFromZeroToN(b));  // a - 1 = -1 here
            XorInt(XorFromZeroToN(-1), XorFromZeroToN(b));
            XorInt(0, XorFromZeroToN(b));
            XorFromZeroToN(b);
        }
    } else {
        // We know that XorRange(a, b) = a XOR (a+1) XOR ... XOR b
        // And we know that XorFromZeroToN(N) = 0 XOR 1 XOR ... XOR N
        // So (XorFromZeroToN(b)) XOR (XorFromZeroToN(a-1))
        // = (0 XOR ... XOR (a-1) XOR a XOR ... XOR b) XOR (0 XOR ... XOR (a-1))
        // = a XOR (a+1) XOR ... XOR b
        // = XorRange(a,b)
        // This relies on the property of XOR that x ^ y ^ y = x
        assert XorRange(a, b) == XorInt(XorFromZeroToN(a - 1), XorFromZeroToN(b));
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
    result := XorInt(XorFromZeroToN(a - 1), XorFromZeroToN(b));
}
// </vc-code>

