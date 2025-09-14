predicate ValidInput(x: int, y: int, z: int)
{
    x >= 1 && y >= 1 && z >= 1 && y + 2 * z <= x
}

function MaxPeople(x: int, y: int, z: int): int
    requires ValidInput(x, y, z)
{
    (x - z) / (y + z)
}

predicate ValidSolution(x: int, y: int, z: int, result: int)
    requires ValidInput(x, y, z)
{
    result == MaxPeople(x, y, z) &&
    result >= 0 &&
    result * (y + z) <= x - z < (result + 1) * (y + z)
}

// <vc-helpers>
lemma DivisionBounds(a: int, d: int)
  requires d > 0
  ensures (a / d) * d <= a
  ensures a < ((a / d) + 1) * d
{
  var q := a / d;
  var r := a % d;
  assert a == q * d + r;
  assert 0 <= r < d;

  calc {
    q * d;
    <= { assert 0 <= r; }
    q * d + r;
    == { assert a == q * d + r; }
    a;
  }

  calc {
    a;
    == { assert a == q * d + r; }
    q * d + r;
    < { assert r < d; }
    q * d + d;
    == { assert q * d + d == (q + 1) * d; }
    (q + 1) * d;
  }
}

lemma DivNonNeg(a: int, d: int)
  requires a >= 0
  requires d > 0
  ensures a / d >= 0
{
  var q := a / d;
  var r := a % d;
  if q < 0 {
    assert a == q * d + r;
    assert 0 <= r < d;
    assert q <= -1;
    assert q * d <= -d;
    calc {
      a;
      == { assert a == q * d + r; }
      q * d + r;
      <= { assert q * d <= -d; }
      -d + r;
    }
    assert -d + r < 0;
    assert a < 0;
    assert false;
  }
  assert q >= 0;
}
// </vc-helpers>

// <vc-spec>
method solve(x: int, y: int, z: int) returns (result: int)
    requires ValidInput(x, y, z)
    ensures ValidSolution(x, y, z, result)
// </vc-spec>
// <vc-code>
{
  result := MaxPeople(x, y, z);

  assert y >= 1;
  assert z >= 1;
  assert y + z > 0;

  // Bounds around the quotient
  DivisionBounds(x - z, y + z);

  // Connect result with the quotient
  assert result == (x - z) / (y + z);

  // Non-negativity of result
  assert x - z >= y + z;
  assert x - z >= 0;
  DivNonNeg(x - z, y + z);
}
// </vc-code>

