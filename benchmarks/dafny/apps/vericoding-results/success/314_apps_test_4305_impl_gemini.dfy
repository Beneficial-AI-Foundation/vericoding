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
lemma lemma_CeilDivProperties(H: int, A: int)
    requires H >= 1 && A >= 1
    ensures CeilDiv(H, A) >= 1
    ensures CeilDiv(H, A) * A >= H
    ensures (CeilDiv(H, A) - 1) * A < H
{
    var attacks := CeilDiv(H, A);

    // Prove attacks >= 1
    assert H >= 1 && A >= 1 ==> H + A - 1 >= A;
    assert attacks >= 1;

    var dividend := H + A - 1;
    var r := dividend % A;
    assert dividend >= 0;
    assert dividend == A * attacks + r && 0 <= r < A;

    // Prove attacks * A >= H
    calc {
        attacks * A;
        == dividend - r;
        == (H + A - 1) - r;
        == H + (A - 1 - r);
    }
    assert r <= A - 1;
    assert A - 1 - r >= 0;
    assert attacks * A >= H;

    // Prove (attacks - 1) * A < H
    calc {
        (attacks - 1) * A;
        == attacks * A - A;
        == (H + A - 1 - r) - A;
        == H - 1 - r;
    }
    assert r >= 0;
    assert (attacks - 1) * A < H;
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
    attacks := CeilDiv(H, A);
    lemma_CeilDivProperties(H, A);
}
// </vc-code>

