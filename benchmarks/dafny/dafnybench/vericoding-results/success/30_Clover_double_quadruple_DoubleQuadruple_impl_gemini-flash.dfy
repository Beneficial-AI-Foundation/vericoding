

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
// </vc-spec>
// <vc-code>
{
  var a' := 2 * x;
  var b' := 4 * x;
  return a', b';
}
// </vc-code>

