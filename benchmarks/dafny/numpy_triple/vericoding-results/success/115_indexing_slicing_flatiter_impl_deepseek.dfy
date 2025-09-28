// <vc-preamble>
// Flat iterator method that creates a flattened view of the input array
// </vc-preamble>

// <vc-helpers>
function flattenArray(a: seq<real>): seq<real> { a }
// </vc-helpers>

// <vc-spec>
method numpy_flatiter(a: seq<real>) returns (result: seq<real>)
  // No special preconditions for creating a flat iterator
  requires true
  // The result preserves all elements in row-major order
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  result := flattenArray(a);
}
// </vc-code>
