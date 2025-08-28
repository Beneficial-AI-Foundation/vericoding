// <vc-helpers>
// No additional helper code or proofs needed for this verification
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures more == x+y
  ensures less == x-y
// </vc-spec>
// </vc-spec>

// <vc-code>
method MultipleReturnsImpl(x: int, y: int) returns (more: int, less: int)
  ensures more == x + y
  ensures less == x - y
{
  more := x + y;
  less := x - y;
}
// </vc-code>
