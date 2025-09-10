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
lemma CeilDivIsMin(H: int, A: int)
    requires ValidInput(H, A)
    ensures IsMinimumAttacks(CeilDiv(H, A), H, A)
{
    var x := H + A - 1;
    var t := x / A;
    var r := x % A;
    // division remainder properties
    assert x == t * A + r;
    assert 0 <= r < A;
    // x >= A because H >= 1
    assert x >= A;
    // rule out t == 0
    if t == 0 {
      assert x == r;
      assert r < A;
      assert x < A;
      assert false;
    }
    assert t >= 1;
    // express H in terms of t and r
    assert H == t * A + r - (A - 1);
    // r <= A-1 implies H <= t*A
    assert r <= A - 1;
    assert H <= t * A;
    // r >= 0 implies (t-1)*A < H
    assert r >= 0;
    assert (t - 1) * A < H;
    // conclude IsMinimumAttacks for CeilDiv(H,A)
    assert CeilDiv(H, A) == t;
    assert CeilDiv(H, A) >= 1;
    assert CeilDiv(H, A) * A >= H;
    assert (CeilDiv(H, A) - 1) * A < H;
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
  CeilDivIsMin(H, A);
}
// </vc-code>

