// <vc-preamble>
function PolyHelperSpec(roots: seq<real>, val: nat): seq<real>
// </vc-preamble>

// <vc-helpers>

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
{
  /* code modified by LLM (iteration 5): Implement polynomial coefficient computation */
  result := new real[roots.Length];
  var i := 0;
  while i < result.Length
    invariant 0 <= i <= result.Length
  {
    result[i] := 0.0;
    i := i + 1;
  }
  result[0] := 1.0;
  
  var j := 0;
  while j < roots.Length
    invariant 0 <= j <= roots.Length
  {
    var k := j;
    while k > 0
      invariant 0 <= k <= j
    {
      result[k] := result[k] - roots[j] * result[k-1];
      k := k - 1;
    }
    j := j + 1;
  }
}
// </vc-code>
