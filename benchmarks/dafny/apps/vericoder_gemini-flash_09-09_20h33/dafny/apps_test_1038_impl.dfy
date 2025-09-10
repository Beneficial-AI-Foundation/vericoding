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

lemma lemma_XorFromZeroToN_properties(n: int)
    requires n >= 0
    ensures XorRange(0, n) == XorFromZeroToN(n) {
    if n == 0 {
        assert XorRange(0, 0) == 0;
        assert XorFromZeroToN(0) == 0;
    } else {
        assert XorRange(0, n) == XorInt(0, XorRange(1, n));
        assert XorInt(0, XorRange(1, n)) == XorRange(1, n);
        lemma_XorFromZeroToN_properties(n-1); // Inductive step
        // We need to prove that XorFromZeroToN(n) == XOR(0..n)
        // This is essentially showing that XorFromZeroToN computes the XOR sum.
    }
}

lemma lemma_XorRange_XorFromZeroToN(a: int, b: int)
    requires 0 <= a <= b
    ensures XorRange(a, b) == XorInt(XorFromZeroToN(a - 1), XorFromZeroToN(b))
{
    if a == 0 {
        calc {
            XorRange(0, b);
            { lemma_XorFromZeroToN_properties(b); }
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
        // The assert statement itself isn't a proof, but the verifier should be able to deduce this
        // from the `calc` proof or the properties of XOR if it's aware of them.
        // For the verifier to accept this, a more formal inductive proof might be needed,
        // or the verifier needs to know the properties of XOR sum.
        // However, the `calc` proof in the a==0 case sets up the base for the verifier.
        // The problem is likely in the `else` branch not having a formal proof.
        // We can leverage the `calc` block here as well, similar to the `a == 0` case
        // by decomposing the problem.
        calc {
            XorRange(a, b);
            // XorRange(a,b) = (0 ^ ... ^ b) ^ (0 ^ ... ^ (a-1)) due to XOR properties
            XorInt(XorRange(0, b), XorRange(0, a - 1));
            { lemma_XorFromZeroToN_properties(b); }
            { lemma_XorFromZeroToN_properties(a - 1); }
            XorInt(XorFromZeroToN(b), XorFromZeroToN(a - 1));
            // Since XOR is commutative, XorInt(A, B) == XorInt(B, A)
            XorInt(XorFromZeroToN(a - 1), XorFromZeroToN(b));
        }

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

