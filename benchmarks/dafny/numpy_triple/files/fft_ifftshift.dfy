// <vc-preamble>
// Method to perform inverse FFT shift on a sequence of real numbers
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ifftshift(x: seq<real>) returns (result: seq<real>)
  requires |x| > 0
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |x| ==> 
    result[i] == x[(i + |x| / 2) % |x|]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
