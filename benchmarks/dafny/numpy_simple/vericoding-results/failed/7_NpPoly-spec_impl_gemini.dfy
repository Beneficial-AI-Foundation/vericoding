// <vc-preamble>
function PolyHelperSpec(roots: seq<real>, val: nat): seq<real>
// </vc-preamble>

// <vc-helpers>
function PolyCoeffs(roots: seq<real>, k: nat, i: nat): real
  requires k <= |roots|
{
  if k == 0 then 0.0
  else if i == 0 then -roots[k-1]
  else if i >= k then 0.0
  else PolyCoeffs(roots, k-1, i) - roots[k-1] * PolyCoeffs(roots, k-1, i-1)
}

function PolyHelperSpec(roots: seq<real>, val: nat): seq<real>
  requires val < |roots|
{
  var n := val + 1;
  seq(|roots|, i => if i >= n then 0.0 else PolyCoeffs(roots, n, i))
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
{
    var n := roots.Length;
    result := new real[n];
    if n > 0 {
        var k: nat := 0;
        while k < n
            invariant 0 <= k <= n
            invariant forall i :: 0 <= i < k ==> result[i] == PolyCoeffs(roots[..], k, i)
            invariant forall i :: k <= i < n ==> result[i] == 0.0
        {
            var r_k := roots[k];
            var i := k;
            while i > 0
                invariant 0 < i <= k
                invariant result[i] == PolyCoeffs(roots[..], k, i) - r_k * PolyCoeffs(roots[..], k, i-1)
                invariant forall j :: i < j < k ==> result[j] == PolyCoeffs(roots[..], k+1, j)
                invariant forall j :: 0 <= j < i ==> result[j] == PolyCoeffs(roots[..], k, j)
            {
                i := i - 1;
                result[i+1] := result[i+1] - r_k * result[i];
            }
            result[0] := result[0] - r_k;
            k := k + 1;
        }
    }
}
// </vc-code>
