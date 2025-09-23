// <vc-preamble>
//PRE-CONDITIONS -> REQUIRES
//POST-CONDITIONS -> ENSURES
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method max(a: int, b: int) returns (z: int)
  requires true
  ensures z >= a || z >= b
// </vc-spec>
// <vc-code>
{
  if a > b {
    z :=a;
  }
  else {
    z := b;
  }
}
// </vc-code>

// 3


// 5a

// 5b

// 5c
// pode dar false e eles nao serem iguais
// 

// 5d