// <vc-preamble>
//PRE-CONDITIONS -> REQUIRES
//POST-CONDITIONS -> ENSURES



// 3


// 5a
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method m1(x: int,y: int) returns (z: int)
  requires 0 < x < y
  ensures z >= 0 && z < y && z != x
// </vc-spec>
// <vc-code>
{
  if (x > 0 && y > 0 && y > x) {
    z := x-1;
  }
}
// </vc-code>

// 5b

// 5c
// pode dar false e eles nao serem iguais
// 

// 5d