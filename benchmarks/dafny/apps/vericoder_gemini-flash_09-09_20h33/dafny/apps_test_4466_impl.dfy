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
lemma MaxPeopleIsNonNegative(x: int, y: int, z: int)
  requires ValidInput(x, y, z)
  ensures MaxPeople(x, y, z) >= 0
{
  assert y + 2 * z <= x;
  assert y >= 1;
  assert z >= 1;
  assert y + z > 0;
  assert x - z >= y + z;
  assert x - z >= 0;
  assert (x - z) / (y + z) >= 0;
}

lemma DivisionProperties(a: int, b: int)
  requires b > 0
  ensures var q := a / b;
          q * b <= a < (q + 1) * b
{}
// </vc-helpers>

// <vc-spec>
method solve(x: int, y: int, z: int) returns (result: int)
    requires ValidInput(x, y, z)
    ensures ValidSolution(x, y, z, result)
// </vc-spec>
// <vc-code>
{
  var y_plus_z := y + z;
  var x_minus_z := x - z;

  MaxPeopleIsNonNegative(x, y, z); // Prove that MaxPeople(x,y,z) is non-negative
  
  // y + z must be positive since y >= 1 and z >= 1
  assert y_plus_z > 0;

  result := x_minus_z / y_plus_z;

  // Use the DivisionProperties lemma to assert the properties of integer division.
  // This asserts result * (y + z) <= x - z < (result + 1) * (y + z)
  DivisionProperties(x_minus_z, y_plus_z);
}
// </vc-code>

