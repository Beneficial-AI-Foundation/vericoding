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
  ensures IsMinimumAttacks(CeilDiv(H, A), H, A)
{
  var atks := CeilDiv(H, A);
  assert atks * A >= H by {
    assert (H + A - 1) / A * A >= H;
    calc {
      atks * A;
      == 
      ((H + A - 1) / A) * A;
      >=
      H;
    }
  }
  if atks > 0 {
    assert (atks - 1) * A < H by {
      assert (H + A - 1) / A - 1 == (H - 1) / A;
      calc {
        (atks - 1) * A;
        ==
        (((H + A - 1) / A) - 1) * A;
        ==
        ((H - 1) / A) * A;
        <=
        H - 1;
        <
        H;
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
  attacks := CeilDiv(H, A);
}
// </vc-code>

