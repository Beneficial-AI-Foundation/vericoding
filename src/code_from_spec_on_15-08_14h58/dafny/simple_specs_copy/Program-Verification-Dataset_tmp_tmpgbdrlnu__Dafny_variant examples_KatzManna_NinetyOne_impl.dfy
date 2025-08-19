// IMPL
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) returns (z: int)
 ensures proveFunctionalPostcondition ==> z == if x > 101 then x-10 else 91
{
  if x > 101 {
    z := x - 10;
  } else {
    z := 91;
  }
}