

// <vc-helpers>
function Multiply(a: int, b: int): int
  requires b >= 0
  ensures Multiply(a,b) == a * b
{
  if b == 0 then 0
  else a + Multiply(a, b - 1)
}
// </vc-helpers>

// <vc-spec>
method Triple (x:int) returns (r:int)
  ensures r==3*x
// </vc-spec>
// <vc-code>
{
  r := x + x + x;
}
// </vc-code>

