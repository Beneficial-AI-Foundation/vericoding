// <vc-preamble>
function PolyHelperSpec(roots: seq<real>, val: nat): seq<real>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed sequence comprehension syntax to use Dafny's seq(length, i => expr) and added decreases clause for termination */
function PolyHelperSpec(roots: seq<real>, val: nat): seq<real>
  decreases val
{
  if val == 0 then [1.0]
  else
    var r := roots[val - 1];
    var prev := PolyHelperSpec(roots, val - 1);
    var newseq := seq(|prev| + 1, i => if i == 0 then -r * prev[0] else if i < |prev| then prev[i - 1] - r * prev[i] else prev[i - 1]);
    newseq
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
/* code modified by LLM (iteration 4): implemented using the helper function */
{
  var helperSeq := PolyHelperSpec(roots[..], (roots.Length - 1) as nat);
  result := new real[roots.Length](i => helperSeq[i]);
}
// </vc-code>
