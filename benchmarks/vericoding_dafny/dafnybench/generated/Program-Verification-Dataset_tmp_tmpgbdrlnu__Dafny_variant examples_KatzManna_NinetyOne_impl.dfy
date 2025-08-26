// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) returns (z: int)
  ensures proveFunctionalPostcondition ==> z == if x > 101 then x-10 else 91;
// </vc-spec>
// <vc-code>
{
  if x > 101 {
    z := x - 10;
  } else {
    z := 91;
  }
}
// </vc-code>