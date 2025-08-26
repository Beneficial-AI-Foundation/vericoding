method max(a: int, b: int) returns (z: int)
  requires true
  ensures z >= a || z >= b
// </vc-spec>
// <vc-code>
{
  if a >= b {
    z := a;
  } else {
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