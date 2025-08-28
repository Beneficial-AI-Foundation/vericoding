// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file shows how to specify and implement a function to compute the
// largest element of a list. The function is fully specified by two
// preconditions, as proved by the MaximumIsUnique lemma below.

// <vc-helpers>
lemma MaximumIsUnique(values: seq<int>, max: int)
  requires values != []
  requires max in values
  requires forall i | 0 <= i < |values| :: values[i] <= max
  ensures forall m | m in values && m > max :: false
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Maximum(values: seq<int>) returns (max: int)
  requires values != []
  ensures max in values
  ensures forall i | 0 <= i < |values| :: values[i] <= max
// </vc-spec>
// </vc-spec>

// <vc-code>
method MaximumImpl(values: seq<int>) returns (max: int)
  requires values != []
  ensures max in values
  ensures forall i | 0 <= i < |values| :: values[i] <= max
{
  max := values[0];
  var i := 1;
  while i < |values|
    invariant 0 <= i <= |values|
    invariant max in values
    invariant forall k | 0 <= k < i :: values[k] <= max
  {
    if values[i] > max {
      max := values[i];
    }
    i := i + 1;
  }
}
// </vc-code>
