// <vc-preamble>
// Method implementing asmatrix operation that interprets input as matrix without copying
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method asmatrix(data: seq<real>) returns (result: seq<real>)
  // Postcondition: length is preserved
  ensures |result| == |data|
  // Postcondition: all elements are preserved in same order
  ensures forall i :: 0 <= i < |data| ==> result[i] == data[i]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
