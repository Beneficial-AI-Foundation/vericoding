

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
// </vc-spec>
// <vc-code>
{
  result := a * b;
}
// </vc-code>

