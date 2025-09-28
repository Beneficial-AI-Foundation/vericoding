// <vc-preamble>
// Flat iterator method that creates a flattened view of the input array
// </vc-preamble>

// <vc-helpers>
function clone_seq(a: seq<real>): seq<real> { a }

lemma clone_seq_preserves(a: seq<real>)
{
  assert clone_seq(a) == a;
  assert |clone_seq(a)| == |a|;
  assert forall i :: 0 <= i < |a| ==> clone_seq(a)[i] == a[i];
}

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
  result := clone_seq(a);
}

// </vc-code>
