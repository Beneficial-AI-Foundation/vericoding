// SPEC
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Cubes(a: array<int>)
 modifies a
 ensures forall i :: 0 <= i < a.Length ==> a[i] == i*i*i
{
}
