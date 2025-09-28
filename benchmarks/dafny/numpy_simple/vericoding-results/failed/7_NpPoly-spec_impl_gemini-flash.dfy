// <vc-preamble>
function PolyHelperSpec(roots: seq<real>, val: nat): seq<real>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add poly helper for specification */
function PolyHelperSpec(roots: seq<real>, val: nat): seq<real>
{
    if val == 0 then
        if |roots| > 0 then [1.0] else []
    else
        var sub_seq := PolyHelperSpec(roots[..val as int], (val - 1) as nat);
        var new_seq := new real[val + 1];
        new_seq[0] := -roots[val - 1] * sub_seq[0];
        for k := 1 to val - 1 {
            new_seq[k] := sub_seq[k-1] - roots[val - 1] * sub_seq[k];
        }
        new_seq[val] := sub_seq[val - 1];
        new_seq[..]
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
/* code modified by LLM (iteration 5): Fixed loop invariants and polynomial multiplication logic to ensure correctness. */
{
    var n := roots.Length;
    result := new real[n];

    if n > 0 {
        result[0] := 1.0;

        var i := 1;
        while i < n
            invariant 1 <= i <= n
            invariant forall k :: 0 <= k < i ==> 
                (var ph_spec := PolyHelperSpec(roots[..i], (i-1) as nat);
                 k < |ph_spec| && result[k] == ph_spec[k])
            invariant forall k :: i <= k < n ==> result[k] == 0.0
        {
            var root_val := roots[i-1];
            var prev_coeff_storage := result[0]; // Store the previous coefficient to be moved

            result[0] := -root_val * result[0];

            var j := 1;
            while j <= i
                invariant 1 <= j <= i
                invariant (var ph_spec := PolyHelperSpec(roots[..i], (i-1) as nat);
                           forall k :: 0 <= k < j ==> k < |ph_spec| && result[k] == ph_spec[k])
                invariant prev_coeff_storage == (if j > 1 then PolyHelperSpec(roots[..i],(i-1) as nat)[j-1] else 1.0)
            {
                var current_val := result[j];
                result[j] := prev_coeff_storage - root_val * current_val;
                prev_coeff_storage := current_val;
                j := j + 1;
            }
            i := i + 1;
        }
    }
}
// </vc-code>
