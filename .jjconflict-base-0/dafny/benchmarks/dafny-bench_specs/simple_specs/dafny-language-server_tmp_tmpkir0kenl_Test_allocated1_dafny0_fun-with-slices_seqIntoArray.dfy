// SPEC
// RUN: %dafny /verifyAllModules /allocated:1 /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This test was contributed by Bryan. It has shown some instabilities in the past.

method seqIntoArray<A>(s: seq<A>, a: array<A>, index: nat)
 requires index + |s| <= a.Length
 modifies a
 ensures a[..] == old(a[..index]) + s + old(a[index + |s|..])
{
}
