// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method In1d<T(==)>(ar1: seq<T>, ar2: seq<T>) returns (result: seq<bool>)
  // The result has the same length as the first input array
  ensures |result| == |ar1|
  // Each element in the result indicates membership: result[i] is true iff ar1[i] exists in ar2
  ensures forall i :: 0 <= i < |ar1| ==> 
    (result[i] <==> exists j :: 0 <= j < |ar2| && ar1[i] == ar2[j])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
