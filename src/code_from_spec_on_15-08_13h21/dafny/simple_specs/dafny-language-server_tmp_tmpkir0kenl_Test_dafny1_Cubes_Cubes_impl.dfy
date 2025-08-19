// IMPL
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Cubes(a: array<int>)
 modifies a
 ensures forall i :: 0 <= i < a.Length ==> a[i] == i*i*i
{
  var j := 0;
  while j < a.Length
    invariant 0 <= j <= a.Length
    invariant forall k :: 0 <= k < j ==> a[k] == k*k*k
  {
    a[j] := j * j * j;
    j := j + 1;
  }
}