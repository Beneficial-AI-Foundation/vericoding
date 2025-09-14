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
lemma LemmaCeilDivIsMinimum(H: int, A: int)
  requires ValidInput(H, A)
  ensures IsMinimumAttacks(CeilDiv(H, A), H, A)
{
  var q := CeilDiv(H, A);
  assert A > 0;
  assert H + A - 1 >= A;
  assert q == (H + A - 1) / A;
  assert q >= A / A;
  assert A / A == 1;
  assert q >= 1;

  var r := (H + A - 1) % A;
  assert H + A - 1 == q * A + r;
  assert 0 <= r < A;

  assert q * A == H + A - 1 - r;
  assert q * A >= H + A - 1 - (A - 1);
  assert q * A >= H;

  assert (q - 1) * A == q * A - A;
  assert (q - 1) * A == (H + A - 1 - r) - A;
  assert (q - 1) * A == H - 1 - r;
  assert (q - 1) * A <= H - 1;
  assert H - 1 < H;
  assert (q - 1) * A < H;

  assert IsMinimumAttacks(q, H, A);
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
  LemmaCeilDivIsMinimum(H, A);
}
// </vc-code>

