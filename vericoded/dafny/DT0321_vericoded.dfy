// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): gradient value at index; handles singleton, boundaries, and interior */
function GAt(f: seq<real>, i: int): real
  requires 0 <= i < |f|
{
  if |f| == 1 then
    0.0
  else if i == 0 then
    f[1] - f[0]
  else if i == |f| - 1 then
    f[|f| - 1] - f[|f| - 2]
  else
    (f[i + 1] - f[i - 1]) / 2.0
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
  /* code modified by LLM (iteration 3): build gradient explicitly handling boundary and interior points without comprehension */
  var n := |f|;
  if n == 1 {
    grad := [0.0];
  } else {
    var res: seq<real> := [];
    // first boundary
    res := res + [f[1] - f[0]];
    var i := 1;
    while i <= n - 2
      invariant 1 <= i <= n - 1
      invariant |res| == i
      invariant res[0] == f[1] - f[0]
      invariant forall j :: 1 <= j < i ==> res[j] == (f[j + 1] - f[j - 1]) / 2.0
      decreases n - 1 - i
    {
      res := res + [ (f[i + 1] - f[i - 1]) / 2.0 ];
      i := i + 1;
    }
    // last boundary
    res := res + [ f[n - 1] - f[n - 2] ];
    grad := res;

    // help Dafny discharge postconditions
    assert |grad| == n;
    assert grad[0] == f[1] - f[0];
    assert grad[n - 1] == f[n - 1] - f[n - 2];
    assert forall i :: 1 <= i < n - 1 ==> grad[i] == (f[i + 1] - f[i - 1]) / 2.0;
  }
}
// </vc-code>
