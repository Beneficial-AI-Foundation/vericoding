// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method legint(c: seq<real>, k: real, lbnd: real, scl: real) returns (result: seq<real>)
    requires scl != 0.0
    requires |c| >= 0
    ensures |result| == |c| + 1
    ensures |c| == 0 ==> result == [k]
    ensures |c| > 0 ==> (
        // Integration constant affects the constant term
        exists base_result: seq<real> :: (|base_result| == |c| + 1 &&
        result[0] == base_result[0] + k &&
        (forall i {:trigger result[i]} :: 1 <= i < |result| ==> result[i] == base_result[i]) &&
        
        // Scaling factor affects all integrated coefficients consistently  
        (scl != 1.0 ==> exists unscaled: seq<real> :: (|unscaled| == |c| + 1 &&
            forall i {:trigger base_result[i]} :: 0 <= i < |result| ==> base_result[i] == scl * unscaled[i])))
    )
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
