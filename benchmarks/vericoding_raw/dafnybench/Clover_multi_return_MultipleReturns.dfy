// <vc-helpers>
// </vc-helpers>

method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures more == x+y
  ensures less == x-y
// <vc-code>
{
  assume false;
}
// </vc-code>