// <vc-preamble>
// Method that copies elements from src to dst where mask is true, 
// preserving dst elements where mask is false
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method copyto<T>(dst: seq<T>, src: seq<T>, mask: seq<bool>) returns (result: seq<T>)
  // All input sequences must have the same length
  requires |dst| == |src| == |mask|
  // Result has the same length as inputs
  ensures |result| == |dst|
  // For each position i, result[i] is src[i] if mask[i] is true, otherwise dst[i]
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] == (if mask[i] then src[i] else dst[i])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
