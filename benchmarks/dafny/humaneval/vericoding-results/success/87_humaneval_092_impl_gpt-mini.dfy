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
function IsInt(x: real): bool {
  x == x.Floor as real
}

function AllInts(x: real, y: real, z: real): bool {
  IsInt(x) && IsInt(y) && IsInt(z)
}

function OneIsSum(x: real, y: real, z: real): bool {
  x == y + z || y == x + z || z == x + y
}
// </vc-helpers>

// <vc-spec>
method any_int(x: real, y: real, z: real) returns (result: bool)
    ensures ValidResult(x, y, z, result)
// </vc-spec>
// <vc-code>
{
  var all := IsInteger(x) && IsInteger(y) && IsInteger(z);
  var one := (x == y + z) || (y == x + z) || (z == x + y);
  result := all && one;
}
// </vc-code>
