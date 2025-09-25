// <vc-preamble>
//PRE-CONDITIONS -> REQUIRES
//POST-CONDITIONS -> ENSURES



// 3


// 5a

// 5b
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method m2(x: nat) returns (y: int)
  requires x <= -1
  ensures y > x && y < x
// </vc-spec>
// <vc-code>
{
  if (x <= -1) {
    y := x+1;
  }
}
// </vc-code>

// 5c
// pode dar false e eles nao serem iguais
// 

// 5d