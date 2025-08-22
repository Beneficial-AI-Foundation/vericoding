// RUN: %dafny /verifyAllModules /allocated:1 /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This test was contributed by Bryan. It has shown some instabilities in the past.

//IMPL seqIntoArray
method seqIntoArray<A>(s: seq<A>, a: array<A>, index: nat)
  requires index + |s| <= a.Length
  modifies a
  ensures a[..] == old(a[..index]) + s + old(a[index + |s|..])
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant a[..] == old(a[..index]) + s[..i] + old(a[index + i..])
  {
    a[index + i] := s[i];
    i := i + 1;
  }
}