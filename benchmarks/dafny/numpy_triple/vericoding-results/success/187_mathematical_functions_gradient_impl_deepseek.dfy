// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function diff(x: real, y: real): real { y - x }
function dblDiv(x: real): real { x / 2.0 }
/* helper modified by LLM (iteration 5): corrected constant function predicate */
predicate IsConstant(f: seq<real>)
  requires |f| >= 1
{
  forall i, j :: 0 <= i < j < |f| ==> f[i] == f[j]
}
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
  /* code modified by LLM (iteration 5): fixed gradient calculation with proper bounds */
  if |f| == 1 {
    grad := [0.0];
  } else {
    grad := [f[1] - f[0]];
    
    var i := 1;
    while i < |f| - 1
      invariant 1 <= i <= |f| - 1
      invariant |grad| == i
      invariant forall k :: 0 <= k < i ==> (
        if k == 0 then grad[k] == f[1] - f[0]
        else if k == |f| - 1 then grad[k] == f[|f|-1] - f[|f|-2]
        else grad[k] == (f[k+1] - f[k-1]) / 2.0
      )
      decreases |f| - 1 - i
    {
      grad := grad + [(f[i+1] - f[i-1]) / 2.0];
      i := i + 1;
    }
    
    grad := grad + [f[|f|-1] - f[|f|-2]];
  }
}
// </vc-code>
