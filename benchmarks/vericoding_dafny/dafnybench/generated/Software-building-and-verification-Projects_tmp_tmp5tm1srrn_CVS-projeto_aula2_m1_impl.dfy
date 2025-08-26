method m1(x: int,y: int) returns (z: int)
  requires 0 < x < y
  ensures z >= 0 && z < y && z != x
// </vc-spec>
// <vc-code>
{
  z := 0;
}
// </vc-code>

// 5b

// 5c
// pode dar false e eles nao serem iguais
// 

// 5d