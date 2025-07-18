// IMPL
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Cubes(a: array<int>)
 modifies a
 ensures forall i :: 0 <= i < a.Length ==> a[i] == i*i*i
{
    var index := 0;
    while index < a.Length
        invariant 0 <= index <= a.Length
        invariant forall j :: 0 <= j < index ==> a[j] == j*j*j
    {
        a[index] := index * index * index;
        index := index + 1;
    }
}