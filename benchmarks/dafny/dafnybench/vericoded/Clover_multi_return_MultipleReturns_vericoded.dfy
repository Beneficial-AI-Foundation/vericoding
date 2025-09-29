

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures more == x+y
  ensures less == x-y
// </vc-spec>
// <vc-code>
{
  more := x + y;
  less := x - y;
}
// </vc-code>

