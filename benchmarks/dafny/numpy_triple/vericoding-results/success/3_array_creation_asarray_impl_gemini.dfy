// <vc-preamble>
/*
 * Dafny specification for numpy.asarray functionality.
 * Converts input sequences to arrays, preserving element order and values.
 * This models the fundamental array creation function that ensures consistent
 * array format regardless of input type.
 */

// Method that converts a sequence to an array representation
// Models numpy.asarray behavior for Vector-based specification
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AsArray(a: seq<real>, n: nat) returns (result: seq<real>)
    // Precondition: input sequence length matches the specified size parameter
    requires |a| == n
    // Postconditions: preserve length, elements, and ordering
    ensures |result| == n
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == a[i]
    ensures forall i :: 0 <= i < n ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  result := a;
}
// </vc-code>
