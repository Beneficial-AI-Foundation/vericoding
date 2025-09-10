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
lemma CeilDivIsMinimum(H: int, A: int)
    requires A > 0 && H >= 1
    ensures IsMinimumAttacks(CeilDiv(H, A), H, A)
{
    var c := CeilDiv(H, A);
    assert c == (H + A - 1) / A;
    
    // Prove c >= 1
    assert H >= 1 && A >= 1;
    assert H + A - 1 >= A;
    assert c >= 1;
    
    // Prove c * A >= H
    assert c * A == ((H + A - 1) / A) * A;
    DivisionLemma(H + A - 1, A);
    assert c * A >= H + A - 1 - (A - 1);
    assert c * A >= H;
    
    // Prove (c - 1) * A < H
    if c > 1 {
        assert (c - 1) * A == c * A - A;
        assert c * A <= H + A - 1;
        assert (c - 1) * A <= H - 1;
        assert (c - 1) * A < H;
    } else {
        assert c == 1;
        assert (c - 1) * A == 0;
        assert 0 < H;
    }
}

lemma DivisionLemma(n: int, d: int)
    requires d > 0
    ensures (n / d) * d <= n < (n / d + 1) * d
{
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
    CeilDivIsMinimum(H, A);
}
// </vc-code>

