method Abs(x:int) returns (y:int)
ensures y>=0;
ensures x>=0 ==> x == y;
ensures x<0 ==> -x == y;
ensures y == abs(x); // use this instead of line 3,4
// </vc-spec>
// <vc-code>
{
  if x >= 0 {
    y := x;
  } else {
    y := -x;
  }
}
// </vc-code>

function abs(x: int): int{
    if x>0 then x else -x
}