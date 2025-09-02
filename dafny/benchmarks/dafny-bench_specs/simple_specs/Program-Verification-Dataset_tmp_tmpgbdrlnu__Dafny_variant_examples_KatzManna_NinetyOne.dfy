// SPEC
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) returns (z: int)
 ensures proveFunctionalPostcondition ==> z == if x > 101 then x-10 else 91
{
}
