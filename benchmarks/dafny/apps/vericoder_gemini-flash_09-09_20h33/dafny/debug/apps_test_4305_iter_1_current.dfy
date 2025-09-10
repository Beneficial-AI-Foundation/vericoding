predicate ValidInput(H: int, A: int)
{
    H >= 1 && A >= 1
}

predicate IsMinimumAttacks(attacks: int, H: int, A: int)
{
    attacks >= 1 &&
    attacks * A >= H &&
    (attacks - 1) * A < H
}

function CeilDiv(H: int, A: int): int
    requires A > 0
{
    (H + A - 1) / A
}

// <vc-helpers>
lemma lemma_ceil_div_is_minimum_attacks(H: int, A: int)
    requires A > 0
    ensures IsMinimumAttacks(CeilDiv(H, A), H, A)
{
    var attacks = CeilDiv(H, A);
    calc {
        (H + A - 1) / A;
        ((H - 1) div A) + 1; // property of integer division: floor(x/y) = x div y for positive y
    }
    // Prove attacks * A >= H
    assert attacks == ((H - 1) div A) + 1;
    // (H - 1) div A <= (H - 1) / A
    // (H - 1) div A * A <= H - 1  (since A > 0)
    // (H - 1) div A * A + A <= H - 1 + A
    // ( (H - 1) div A + 1 ) * A <= H + A - 1
    // attacks * A <= H + A - 1  (This is not what we want directly.)

    // Let's use properties of '/' operator directly.
    // (H + A - 1) / A >= H/A if H is not a multiple of A
    // (H + A - 1) / A * A >= H always
    assert (H + A - 1) / A * A >= H; // This is a standard property of integer division (x/y)*y >= x if x is positive


    // Prove (attacks - 1) * A < H
    // attacks - 1 = (H + A - 1) / A - 1
    // (H + A - 1) / A - 1 * A < H?

    // From definition of integer division:
    // x div y <= x / y
    // (H + A - 1) div A  is the smallest integer `k` such that `k * A >= H`
    // (H + A - 1) div A * A >= H
    // ((H + A - 1) div A - 1) * A < H

    calc {
        attacks - 1;
        (H + A - 1) / A - 1;
    }
    // We know: (H + A - 1) / A * A >= H
    // and ((H + A - 1) / A - 1) * A < H for integer division.
    assert (attacks - 1) * A < H;
    assert attacks >= 1 by {
        if H >= 1 && A >= 1 {
            assert (H + A - 1) / A >= 1 by {
                if H + A - 1 < A { // This implies H < 1, which contradicts H >= 1
                    assert H + A - 1 < A;
                    assert H < 1;
                    assert false;
                }
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(H: int, A: int) returns (attacks: int)
    requires ValidInput(H, A)
    ensures IsMinimumAttacks(attacks, H, A)
    ensures attacks == CeilDiv(H, A)
// </vc-spec>
// <vc-code>
{
    var c = CeilDiv(H, A);
    lemma_ceil_div_is_minimum_attacks(H, A);
    attacks := c;
}
// </vc-code>

