// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): contains predicate to check if element exists in sequence */
predicate contains(seq: seq<int>, elem: int)
{
    exists i :: 0 <= i < |seq| && seq[i] == elem
}

/* helper modified by LLM (iteration 5): lemma to help prove containment properties */
lemma ContainmentLemma(s: seq<int>, result: seq<int>, i: int, elem: int)
    requires 0 <= i < |s|
    requires elem == s[i]
    requires forall j :: 0 <= j < i ==> contains(result, s[j])
    requires !contains(result, elem)
    ensures contains(result + [elem], s[i])
{
    assert (result + [elem])[|result|] == elem;
}
// </vc-helpers>

// <vc-spec>
method SetToSeq(s: seq<int>) returns (result: seq<int>)
    ensures
        // All elements are unique in the result  
        forall i: int, j: int :: 0 <= i < j < |result| ==> result[i] != result[j]
    ensures
        // Every element in result is in s
        forall i: int :: 0 <= i < |result| ==> 
            exists j: int :: 0 <= j < |s| && s[j] == result[i]
    ensures
        // Every element in s is in result
        forall i: int :: 0 <= i < |s| ==> 
            exists j: int :: 0 <= j < |result| && result[j] == s[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop invariants and added proper bounds checking */
    result := [];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k, l :: 0 <= k < l < |result| ==> result[k] != result[l]
        invariant forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < |s| && s[j] == result[k]
        invariant forall j :: 0 <= j < i ==> exists k :: 0 <= k < |result| && result[k] == s[j]
    {
        var found := false;
        var j := 0;
        while j < |result|
            invariant 0 <= j <= |result|
            invariant found <==> exists k :: 0 <= k < j && result[k] == s[i]
        {
            if result[j] == s[i] {
                found := true;
                break;
            }
            j := j + 1;
        }
        if !found {
            result := result + [s[i]];
        }
        i := i + 1;
    }
}
// </vc-code>
