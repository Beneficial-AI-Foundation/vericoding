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
  var x_is_int := IsInteger(x);
  var y_is_int := IsInteger(y);
  var z_is_int := IsInteger(z);
  
  if !x_is_int || !y_is_int || !z_is_int {
    result := false;
    return;
  }
  
  var sum_condition := (x == y + z) || (y == x + z) || (z == x + y);
  result := sum_condition;
}
// </vc-code>
