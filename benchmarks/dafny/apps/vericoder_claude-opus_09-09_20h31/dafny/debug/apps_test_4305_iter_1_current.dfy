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
lemma CeilDivCorrect(H: int, A: int)
    requires A > 0
    requires H >= 1
    ensures var c := CeilDiv(H, A); c >= 1 && c * A >= H && (c - 1) * A < H
{
    var c := CeilDiv(H, A);
    var c' := (H + A - 1) / A;
    assert c == c';
    
    // Prove c >= 1
    assert H >= 1;
    assert H + A - 1 >= A;
    assert (H + A - 1) / A >= 1;
    assert c >= 1;
    
    // Prove c * A >= H
    var r := (H + A - 1) % A;
    assert H + A - 1 == c * A + r;
    assert 0 <= r < A;
    assert H == c * A + r - A + 1;
    assert H <= c * A + r;
    assert H <= c * A + (A - 1);
    
    if r == 0 {
        assert H + A - 1 == c * A;
        assert H == c * A - A + 1;
        assert H <= c * A;
    } else {
        assert r >= 1;
        assert H == c * A + r - A + 1;
        assert H <= c * A;
    }
    assert c * A >= H;
    
    // Prove (c - 1) * A < H
    assert c * A >= H;
    assert c * A - A < H + A - 1;
    assert (c - 1) * A < H;
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
    CeilDivCorrect(H, A);
}
// </vc-code>

