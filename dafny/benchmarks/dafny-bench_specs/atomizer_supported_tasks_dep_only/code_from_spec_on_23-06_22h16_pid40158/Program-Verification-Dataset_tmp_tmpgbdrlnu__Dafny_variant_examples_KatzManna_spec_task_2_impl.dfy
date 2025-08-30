// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

//ATOM_PLACEHOLDER_NinetyOne

//IMPL Gcd
method Gcd(x1: int, x2: int)
  requires 1 <= x1 && 1 <= x2;
{
  var a := x1;
  var b := x2;
  
  while b != 0
    invariant a > 0 && b >= 0
  {
    var temp := a % b;
    a := b;
    b := temp;
  }
}

//ATOM_PLACEHOLDER_Determinant