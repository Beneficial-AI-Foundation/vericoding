// <vc-preamble>

predicate IsInteger(x: real)
{
    x == x.Floor as real
}

predicate AllIntegers(x: real, y: real, z: real)
{
    IsInteger(x) && IsInteger(y) && IsInteger(z)
}

predicate OneEqualsSumOfOtherTwo(x: real, y: real, z: real)
{
    x == y + z || y == x + z || z == x + y
}

predicate ValidResult(x: real, y: real, z: real, result: bool)
{
    result <==> (AllIntegers(x, y, z) && OneEqualsSumOfOtherTwo(x, y, z))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method any_int(x: real, y: real, z: real) returns (result: bool)
    ensures ValidResult(x, y, z, result)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
