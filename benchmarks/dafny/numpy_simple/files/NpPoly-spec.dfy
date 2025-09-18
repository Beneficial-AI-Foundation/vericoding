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
    assume {:axiom} false;
}
// </vc-code>
