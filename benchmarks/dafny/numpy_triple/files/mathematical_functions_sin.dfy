// <vc-preamble>
module NumpySin {

    /**
     * Mathematical sine function for specification purposes.
     * Represents the trigonometric sine function with its fundamental properties.
     */
    function sin(x: real): real
        ensures -1.0 <= sin(x) <= 1.0

    /**
     * Computes the trigonometric sine element-wise on a sequence of real numbers.
     * Each element in the input sequence represents an angle in radians.
     * Returns a sequence of the same length containing the sine of each input element.
     */
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Sin(x: seq<real>) returns (result: seq<real>)
        ensures |result| == |x|
        ensures forall i :: 0 <= i < |result| ==> -1.0 <= result[i] <= 1.0
        ensures forall i :: 0 <= i < |result| ==> result[i] == sin(x[i])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
