method m3(x: int,y: int) returns (z: bool)
  ensures z ==> x==y
// </vc-spec>
// <vc-code>
{
  z := x == y;
}
// </vc-code>

// 5d