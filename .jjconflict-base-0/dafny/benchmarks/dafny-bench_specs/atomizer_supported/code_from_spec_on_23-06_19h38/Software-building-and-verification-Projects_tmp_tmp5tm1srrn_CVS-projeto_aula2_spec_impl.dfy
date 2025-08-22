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

//IMPL m1
method m1(x: int,y: int) returns (z: int)
  requires 0 < x < y
  ensures z >= 0 && z < y && z != x
{
  if x == 1 {
    z := 0;
  } else {
    z := 1;
  }
}

//IMPL m2
method m2(x: nat) returns (y: int)
  requires x <= -1
  ensures y > x && y < x
{
  // This method has contradictory ensures clauses (y > x && y < x)
  // and an impossible precondition (x: nat but x <= -1)
  // Since nat means x >= 0, the precondition x <= -1 is impossible
  // This means the method will never be called, so any implementation works
  y := 0;
}

//IMPL m3
method m3(x: int,y: int) returns (z: bool)
  ensures z ==> x==y
{
  z := x == y;
}

//IMPL m4
method m4(x: int,y: int) returns (z: bool)
  ensures z ==> x==y && x==y ==> z
{
  z := x == y;
}