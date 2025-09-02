// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

//ATOM_PLACEHOLDER_NinetyOne

// SPEC 

method Gcd(x1: int, x2: int)
  requires 1 <= x1 && 1 <= x2;
{
}


//ATOM_PLACEHOLDER_Determinant



