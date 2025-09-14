// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Contains(xs: seq<int>, y: int): bool {
    if |xs| == 0 then false
    else if xs[0] == y then true
    else Contains(xs[1..], y)
}
predicate NoDuplicates(xs: seq<int>)
{
    forall i, j :: 0 <= i < j < |xs| ==> xs[i] != xs[j]
}
lemma SequenceMatchLemma(result: seq<int>, xs: seq<int>, e: int, i: int)
    requires forall k :: 0 <= k < i && xs[k] <= e ==> Contains(result, xs[k])
    requires forall k :: 0 <= k < |result| ==> result[k] <= e && Contains(xs, result[k])
    ensures forall k :: 0 <= k < i && xs[k] <= e ==> xs[k] in result
{
    // Prove that if Contains holds, then element is in sequence
    forall k | 0 <= k < i && xs[k] <= e
        ensures xs[k] in result
    {
        if xs[k] !in result {
            // Contradiction: Contains says it should be in result
            assert Contains(result, xs[k]) ==> xs[k] in result;
        }
    }
}
/* helper modified by LLM (iteration 5): added proof body to SequenceMatchLemma */
// </vc-helpers>

// <vc-spec>
method RemoveAllGreater(v: array<int>, e: int) returns (result: array<int>)

    requires 
        forall k1, k2 :: 0 <= k1 < k2 < v.Length ==> v[k1] != v[k2]

    ensures
        forall k :: 0 <= k < result.Length ==> result[k] <= e && result[k] in v[..]
    ensures
        forall k :: 0 <= k < v.Length && v[k] <= e ==> v[k] in result[..]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed array bounds and verification */
    var xs := v[..];
    result := new int[0];
    var i := 0;
    
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant forall k :: 0 <= k < result.Length ==> result[k] <= e && Contains(xs, result[k])
        invariant forall k :: 0 <= k < i && v[k] <= e ==> Contains(result[..], v[k])
        invariant NoDuplicates(result[..])
    {
        if v[i] <= e {
            var newLen := result.Length + 1;
            var newResult := new int[newLen];
            var j := 0;
            while j < result.Length
                invariant 0 <= j <= result.Length
                invariant forall k :: 0 <= k < j ==> newResult[k] == result[k]
                invariant NoDuplicates(newResult[..j])
            {
                newResult[j] := result[j];
                j := j + 1;
            }
            newResult[result.Length] := v[i];
            result := newResult;
        }
        i := i + 1;
    }
    
    SequenceMatchLemma(result[..], xs, e, v.Length);
}
// </vc-code>
