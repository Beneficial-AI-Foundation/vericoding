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
lemma DivUnique(a: int, b: int, q: int)
  requires b > 0 && 0 <= q && q * b <= a && a < (q + 1) * b
  ensures q == a / b
{
  var qprime := a / b;
  var r := a % b;
  assert a == qprime * b + r;
  assert 0 <= r < b;

  if qprime >= q + 1 {
    // qprime * b >= (q+1) * b > a, but qprime * b <= a (since r >= 0) -> contradiction
    assert qprime * b >= (q + 1) * b;
    assert (q + 1) * b > a;
    assert qprime * b > a;
    assert qprime * b <= a;
    assert false;
  }

  if qprime <= q - 1 {
    // qprime * b + r <= (q-1)*b + (b-1) = q*b - 1 < q*b <= a -> contradiction with a == qprime*b + r
    assert qprime * b + r <= (q - 1) * b + (b - 1);
    assert (q - 1) * b + (b - 1) == q * b - 1;
    assert q * b <= a;
    assert qprime * b + r < q * b;
    assert a == qprime * b + r;
    assert false;
  }

  // Neither qprime >= q+1 nor qprime <= q-1 holds, so qprime == q
  assert qprime == q;
}
// </vc-helpers>

// <vc-spec>
method solve(x: int, y: int, z: int) returns (result: int)
    requires ValidInput(x, y, z)
    ensures ValidSolution(x, y, z, result)
// </vc-spec>
// <vc-code>
{
  var a := x - z;
  var b := y + z;
  result := 0;
  while (result + 1) * b <= a
    invariant 0 <= result
    invariant result * b <= a
    decreases a - result * b
  {
    result := result + 1;
  }
  DivUnique(a, b, result);
}
// </vc-code>

