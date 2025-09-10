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
  
  // Prove atks >= 1
  assert atks >= 1 by {
    assert H >= 1;  // From ValidInput
    assert (H + A - 1) >= A;  // Since H >= 1, A >= 1
    assert (H + A - 1) / A >= 1;  // Since (H + A - 1) >= A and A > 0
  }
  
  // Prove atks * A >= H
  assert atks * A >= H by {
    calc {
      atks * A;
      ==
      ((H + A - 1) / A) * A;
      >=
      (H + A - 1) - (A - 1);  // Because integer division truncates
      ==
      H;
    }
  }
  
  // Prove (atks - 1) * A < H
  assert (atks - 1) * A < H by {
    calc {
      (atks - 1) * A;
      ==
      (((H + A - 1) / A) - 1) * A;
      <=
      ((H + A - 1) / A - 1) * A + (A - 1);  // Add remainder
      ==
      ((H + A - 1) / A) * A - A + (A - 1);
      ==
      ((H + A - 1) / A) * A - 1;
      <=
      (H + A - 1) - 1;  // Since (x/A)*A ≤ x
      ==
      H + A - 2;
      <
      H + A - 1;
    }
    // More direct approach
    assert (atks - 1) * A < H by {
      assert atks == (H + A - 1) / A;
      assert (atks - 1) * A < H by {
        assert (H + A - 1) / A <= (H + A - 1) / A;
        assert ((H + A - 1) / A - 1) * A < H;
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
  attacks := (H + A - 1) / A;
  CeilDivIsMinimumAttacks(H, A);
}
// </vc-code>

