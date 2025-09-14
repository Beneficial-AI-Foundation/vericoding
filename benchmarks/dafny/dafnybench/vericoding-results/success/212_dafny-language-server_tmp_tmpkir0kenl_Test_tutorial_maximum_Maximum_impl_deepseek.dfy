// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file shows how to specify and implement a function to compute the
// largest element of a list. The function is fully specified by two
// preconditions, as proved by the MaximumIsUnique lemma below.

// <vc-helpers>
lemma MaximumIsUnique(values: seq<int>, max1: int, max2: int)
  requires values != []
  requires max1 in values && forall i | 0 <= i < |values| :: values[i] <= max1
  requires max2 in values && forall i | 0 <= i < |values| :: values[i] <= max2
  ensures max1 == max2
{
}
// </vc-helpers>

// <vc-spec>
method Maximum(values: seq<int>) returns (max: int)
  requires values != []
  ensures max in values
  ensures forall i | 0 <= i < |values| :: values[i] <= max
// </vc-spec>
// <vc-code>
{
  max := values[0];
  var index := 1;
  
  while index < |values|
    invariant 0 < index <= |values|
    invariant max in values[..index]
    invariant forall i | 0 <= i < index :: values[i] <= max
  {
    if values[index] > max {
      max := values[index];
    }
    index := index + 1;
  }
}
// </vc-code>

