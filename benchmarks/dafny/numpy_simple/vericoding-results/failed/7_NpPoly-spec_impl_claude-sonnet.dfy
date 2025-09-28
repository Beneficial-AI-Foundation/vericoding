// <vc-preamble>
function PolyHelperSpec(roots: seq<real>, val: nat): seq<real>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate function declaration since it's already in preamble */
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
  /* code modified by LLM (iteration 5): fixed to ensure helperSeq has same length and proper array access */
  var helperSeq := PolyHelperSpec(roots[..], (roots.Length - 1) as nat);
  result := new real[roots.Length];
  var i := 0;
  while i < roots.Length
    invariant 0 <= i <= roots.Length
    invariant result.Length == roots.Length
    invariant |helperSeq| == roots.Length
    invariant forall j :: 0 <= j < i ==> result[j] == helperSeq[j]
  {
    result[i] := helperSeq[i];
    i := i + 1;
  }
}
// </vc-code>
