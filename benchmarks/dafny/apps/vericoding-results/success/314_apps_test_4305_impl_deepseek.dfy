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
lemma CeilDivIsMinimumAttacks(H: int, A: int)
  requires A > 0
  requires H >= 1
  ensures IsMinimumAttacks(CeilDiv(H, A), H, A)
{
  var atks := CeilDiv(H, A);
  
  // Prove atks >= 1
  assert atks >= 1 by {
    assert H >= 1;
    assert (H + A - 1) >= A;
    assert (H + A - 1) / A >= 1;
  }
  
  // Prove atks * A >= H
  assert atks * A >= H by {
    calc {
      atks * A;
      ==
      ((H + A - 1) / A) * A;
      >=
      H + A - 1 - (A - 1);
      ==
      H;
    }
  }
  
  // Prove (atks - 1) * A < H
  assert (atks - 1) * A < H by {
    var x := H + A - 1;
    assert (x / A) * A <= x;
    assert ((x / A) - 1) * A <= x - A;
    assert x - A < H;
    assert ((x / A) - 1) * A < H;
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
  attacks := (H + A - 1) / A;
  CeilDivIsMinimumAttacks(H, A);
}
// </vc-code>

