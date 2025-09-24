// <vc-preamble>
//PRE-CONDITIONS -> REQUIRES
//POST-CONDITIONS -> ENSURES



// 3


// 5a

// 5b

// 5c
// pode dar false e eles nao serem iguais
// 

// 5d
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method m4(x: int,y: int) returns (z: bool)
  ensures z ==> x==y && x==y ==> z
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
