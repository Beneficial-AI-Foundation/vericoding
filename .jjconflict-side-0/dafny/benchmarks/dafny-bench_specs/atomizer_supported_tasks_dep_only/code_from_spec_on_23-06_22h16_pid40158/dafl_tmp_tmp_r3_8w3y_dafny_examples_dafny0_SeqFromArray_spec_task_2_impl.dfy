// RUN: %dafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// /autoTriggers:1 added to suppress instabilities

//ATOM_PLACEHOLDER_Main

//IMPL H
method H(a: array<int>, c: array<int>, n: nat, j: nat)
  requires j < n == a.Length == c.Length
{
}

//ATOM_PLACEHOLDER_K

//ATOM_PLACEHOLDER_L

//ATOM_PLACEHOLDER_M

//ATOM_PLACEHOLDER_M'