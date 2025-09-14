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
    requires H >= 1 && A > 0
    ensures IsMinimumAttacks(CeilDiv(H, A), H, A)
{
    var attacks := CeilDiv(H, A);
    // Prove attacks * A >= H
    assert (H + A - 1) / A * A >= H;

    // Prove (attacks - 1) * A < H
    // We want to show ((H + A - 1) / A - 1) * A < H
    // Let k = (H + A - 1) / A. We know k * A >= H.
    // We also know that k - 1 is the largest integer such that (k - 1) * A < H.
    // This is a property of integer division.
    // (X / Y) * Y <= X if Y < 0
    // (X / Y) * Y > X - Y (for X = H + A - 1, Y = A)
    // (H + A - 1) / A * A > (H + A - 1) - A
    // (H + A - 1) / A * A > H - 1
    // (H + A - 1) / A * A >= H

    // To prove (attacks - 1) * A < H, consider:
    // (attacks - 1) * A = ((H + A - 1) / A - 1) * A
    // By integer division properties: (X / Y) * Y <= X.
    // So, ((H + A - 1) div A) * A <= H + A - 1
    // and ((H + A - 1) div A - 1) * A <= (H + A - 1) - A = H - 1 < H
    // This is because (X div Y - 1) * Y < X.
    assert (attacks - 1) * A < H;

    // Prove attacks >= 1
    assert attacks >= 1 by {
        if H >= 1 && A >= 1 {
            assert H + A - 1 >= A; // Since H >= 1
            assert (H + A - 1) / A >= 1;
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
    var c := CeilDiv(H, A);
    lemma_ceil_div_is_minimum_attacks(H, A);
    attacks := c;
}
// </vc-code>

