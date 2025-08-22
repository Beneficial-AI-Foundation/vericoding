//IMPL max
method max(a: int, b: int) returns (z: int)
  requires true
  ensures z >= a || z >= b
{
  if a >= b {
    z := a;
  } else {
    z := b;
  }
}

//IMPL Main
method Main() {
}

// 3
//ATOM_PLACEHOLDER_mystery1

//ATOM_PLACEHOLDER_mystery2

// 5a
//ATOM_PLACEHOLDER_m1

// 5b
//ATOM_PLACEHOLDER_m2

// 5c
// pode dar false e eles nao serem iguais
// 
//ATOM_PLACEHOLDER_m3

// 5d
//ATOM_PLACEHOLDER_m4