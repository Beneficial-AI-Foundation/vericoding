//ATOM_PLACEHOLDER_max

//ATOM_PLACEHOLDER_Main

// 3
//IMPL mystery1
method mystery1(n: nat,m: nat) returns (res: nat)
  ensures n+m == res
{
  res := n + m;
}

//IMPL mystery2
method mystery2(n: nat,m: nat) returns (res: nat)
  ensures n*m == res
{
  res := n * m;
}

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