// RUN: %dafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// /autoTriggers:1 added to suppress instabilities

//ATOM_PLACEHOLDER_Main

//ATOM_PLACEHOLDER_H

//ATOM_PLACEHOLDER_K

// SPEC 

method L(a: array<int>, c: array<int>, n: nat)
  requires n <= a.Length == c.Length
{
}


//ATOM_PLACEHOLDER_M

//ATOM_PLACEHOLDER_M'



