//ATOM_PLACEHOLDER_max

//ATOM_PLACEHOLDER_Main

// 3
//ATOM_PLACEHOLDER_mystery1

//ATOM_PLACEHOLDER_mystery2

// 5a
//IMPL m1
method m1(x: int,y: int) returns (z: int)
  requires 0 < x < y
  ensures z >= 0 && z < y && z != x
{
  if x == 1 {
    z := 0;
  } else {
    z := x - 1;
  }
}

// 5b
//ATOM_PLACEHOLDER_m2

// 5c
// pode dar false e eles nao serem iguais
// 
//ATOM_PLACEHOLDER_m3

// 5d
//ATOM_PLACEHOLDER_m4