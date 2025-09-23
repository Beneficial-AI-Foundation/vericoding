// <vc-preamble>
//PRE-CONDITIONS -> REQUIRES
//POST-CONDITIONS -> ENSURES



// 3


// 5a

// 5b

// 5c
// pode dar false e eles nao serem iguais
//
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method m3(x: int,y: int) returns (z: bool)
  ensures z ==> x==y
// </vc-spec>
// <vc-code>
{
  if (x == y) {
    z := true;
  }
  else {
    z := false;
  }
}
// </vc-code>

// 5d