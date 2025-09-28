// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no helpers needed */
// </vc-helpers>

// <vc-spec>
method NumpyGradient(f: seq<real>) returns (grad: seq<real>)
  requires |f| >= 1  // Input array must be non-empty
  ensures |grad| == |f|  // Output has same size as input
  
  // Single point case: gradient is zero
  ensures |f| == 1 ==> grad[0] == 0.0
  
  // Multi-point case: boundary and interior conditions
  ensures |f| > 1 ==> (
    // First boundary: forward difference grad[0] = f[1] - f[0]
    grad[0] == f[1] - f[0] &&
    
    // Last boundary: backward difference grad[n] = f[n] - f[n-1]
    grad[|f|-1] == f[|f|-1] - f[|f|-2] &&
    
    // Interior points: central difference grad[i] = (f[i+1] - f[i-1]) / 2
    (forall i :: 1 <= i < |f|-1 ==> 
      grad[i] == (f[i+1] - f[i-1]) / 2.0)
  )
  
  // Mathematical property: for constant functions, gradient is zero everywhere
  ensures (forall i :: 0 <= i < |f| ==> f[i] == f[0]) ==> 
          (forall i :: 0 <= i < |f| ==> grad[i] == 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): correct gradient construction using sequence comprehension */
  if |f| == 1 {
    grad := [0.0];
  } else {
    var n := |f|;
    grad := seq(n, i requires 0 <= i < n => 
      if i == 0 then f[1] - f[0]
      else if i == n-1 then f[n-1] - f[n-2]
      else (f[i+1] - f[i-1]) / 2.0
    );
  }
}
// </vc-code>
