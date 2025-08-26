method mult(a:int, b:int) returns (x:int)
    requires a >= 0 && b >= 0
    ensures x == a * b
// </vc-spec>
// <vc-code>
{
  x := 0;
  var i := 0;
  while i < b
    invariant 0 <= i <= b
    invariant x == a * i
  {
    x := x + a;
    i := i + 1;
  }
}
// </vc-code>