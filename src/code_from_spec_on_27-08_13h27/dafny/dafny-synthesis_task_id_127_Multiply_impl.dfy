// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
// </vc-spec>
// </vc-spec>

// <vc-code>
method MultiplyImpl(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}
// </vc-code>
