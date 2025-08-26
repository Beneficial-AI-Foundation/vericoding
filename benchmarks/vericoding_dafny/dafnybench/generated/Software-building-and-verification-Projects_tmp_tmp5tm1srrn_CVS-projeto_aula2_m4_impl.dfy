method m4(x: int,y: int) returns (z: bool)
  ensures z ==> x==y && x==y ==> z
// </vc-spec>
// <vc-code>
{
  z := x == y;
}
// </vc-code>