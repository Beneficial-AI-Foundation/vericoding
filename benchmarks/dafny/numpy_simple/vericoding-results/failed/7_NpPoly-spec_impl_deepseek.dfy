// <vc-preamble>
function PolyHelperSpec(roots: seq<real>, val: nat): seq<real>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed termination condition and postconditions */ function PolyHelperSpec(roots: seq<real>, val: nat): seq<real>
  requires |roots| > 0 && val < |roots|
  ensures |result| == val + 1
  ensures val + 1 <= |roots| ==> result[0] == 1.0
{
  if val == 0 then [1.0 - roots[0]]
  else [1.0] + PolyHelperSpec(roots[1..], val - 1)
}

lemma PolyHelperLemma(roots: seq<real>, val: nat)
  requires |roots| > 0 && val < |roots|
  ensures |PolyHelperSpec(roots, val)| == val + 1
  ensures val + 1 <= |roots| ==> PolyHelperSpec(roots, val)[0] == 1.0
  decreases val
{
  if val > 0 {
    PolyHelperLemma(roots[1..], val - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method PolyHelper(roots: array<real>, val: nat) returns (result: array<real>)
    requires 
        roots.Length > 0 &&
        val > 0
    ensures 
        result.Length == roots.Length &&
        (result.Length > 0 ==> result[0] == 1.0)
{
    assume {:axiom} false;
}

method Poly(roots: array<real>) returns (result: array<real>)
    requires roots.Length > 0
    ensures 
        result.Length == roots.Length &&
        (var helperSeq := PolyHelperSpec(roots[..], (roots.Length - 1) as nat);
         |helperSeq| == result.Length &&
         forall i :: 0 <= i < result.Length ==> result[i] == helperSeq[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix polynomial generation with correct convolution algorithm */
{
    ghost var rootsSeq := roots[..];
    var n := roots.Length;
    var poly := new real[n];
    poly[0] := 1.0;
    
    for i := 1 to n - 1 {
        poly[i] := 0.0;
    }
    
    for k := 0 to n - 1 {
        var newPoly := new real[n];
        for i := 0 to n - 1 {
            if i == 0 {
                newPoly[0] := -roots[k] * poly[0];
            } else {
                newPoly[i] := poly[i - 1] - roots[k] * poly[i];
            }
        }
        poly := newPoly;
    }
    
    result := poly;
}
// </vc-code>
