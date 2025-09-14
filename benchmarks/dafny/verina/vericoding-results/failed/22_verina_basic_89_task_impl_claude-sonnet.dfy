// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate contains(s: seq<int>, x: int)
{
    exists i :: 0 <= i < |s| && s[i] == x
}

/* helper modified by LLM (iteration 5): strengthened to prove element relationships */
lemma AppendPreservesUniqueness(result: seq<int>, x: int)
    requires forall k, l :: 0 <= k < l < |result| ==> result[k] != result[l]
    requires !contains(result, x)
    ensures forall k, l :: 0 <= k < l < |result + [x]| ==> (result + [x])[k] != (result + [x])[l]
    ensures forall k :: 0 <= k < |result + [x]| ==> exists j :: 0 <= j < |result| || k == |result|
{
    var new_result := result + [x];
    forall k, l | 0 <= k < l < |new_result|
        ensures new_result[k] != new_result[l]
    {
        if l == |result| {
            assert new_result[l] == x;
            assert new_result[k] == result[k];
            assert !contains(result, x);
        } else {
            assert new_result[k] == result[k];
            assert new_result[l] == result[l];
        }
    }
}

/* helper modified by LLM (iteration 5): proper bidirectional proof */
lemma AllElementsProcessed(s: seq<int>, result: seq<int>, i: int)
    requires i == |s|
    requires forall j :: 0 <= j < i ==> exists k :: 0 <= k < |result| && result[k] == s[j]
    requires forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < i && s[j] == result[k]
    ensures forall j :: 0 <= j < |s| ==> exists k :: 0 <= k < |result| && result[k] == s[j]
    ensures forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < |s| && s[j] == result[k]
{
    assert i == |s|;
}

/* helper modified by LLM (iteration 5): maintains bidirectional invariant when element exists */
lemma LoopInvariantMaintained(s: seq<int>, result: seq<int>, i: int)
    requires 0 <= i < |s|
    requires forall j :: 0 <= j < i ==> exists k :: 0 <= k < |result| && result[k] == s[j]
    requires forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < |s| && s[j] == result[k]
    requires contains(result, s[i])
    ensures forall j :: 0 <= j < i + 1 ==> exists k :: 0 <= k < |result| && result[k] == s[j]
    ensures forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < |s| && s[j] == result[k]
{
    forall j | 0 <= j < i + 1
        ensures exists k :: 0 <= k < |result| && result[k] == s[j]
    {
        if j == i {
            assert contains(result, s[i]);
            var k :| 0 <= k < |result| && result[k] == s[i];
        }
    }
}

/* helper modified by LLM (iteration 5): maintains bidirectional invariant when element is added */
lemma ElementAddedInvariant(s: seq<int>, result: seq<int>, new_result: seq<int>, i: int)
    requires 0 <= i < |s|
    requires forall j :: 0 <= j < i ==> exists k :: 0 <= k < |result| && result[k] == s[j]
    requires forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < |s| && s[j] == result[k]
    requires new_result == result + [s[i]]
    requires !contains(result, s[i])
    ensures forall j :: 0 <= j < i + 1 ==> exists k :: 0 <= k < |new_result| && new_result[k] == s[j]
    ensures forall k :: 0 <= k < |new_result| ==> exists j :: 0 <= j < |s| && s[j] == new_result[k]
{
    forall j | 0 <= j < i + 1
        ensures exists k :: 0 <= k < |new_result| && new_result[k] == s[j]
    {
        if j == i {
            assert new_result[|result|] == s[i];
        } else {
            assert j < i;
            var k :| 0 <= k < |result| && result[k] == s[j];
            assert new_result[k] == s[j];
        }
    }
    
    forall k | 0 <= k < |new_result|
        ensures exists j :: 0 <= j < |s| && s[j] == new_result[k]
    {
        if k == |result| {
            assert new_result[k] == s[i];
            assert 0 <= i < |s|;
        } else {
            assert k < |result|;
            assert new_result[k] == result[k];
            var j :| 0 <= j < |s| && s[j] == result[k];
        }
    }
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
    /* code modified by LLM (iteration 5): strengthened invariants and proof obligations */
    result := [];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k, l :: 0 <= k < l < |result| ==> result[k] != result[l]
        invariant forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < |s| && s[j] == result[k]
        invariant forall j :: 0 <= j < i ==> exists k :: 0 <= k < |result| && result[k] == s[j]
        invariant forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < i && s[j] == result[k]
    {
        if !contains(result, s[i]) {
            AppendPreservesUniqueness(result, s[i]);
            var old_result := result;
            result := result + [s[i]];
            ElementAddedInvariant(s, old_result, result, i);
        } else {
            LoopInvariantMaintained(s, result, i);
        }
        i := i + 1;
    }
    AllElementsProcessed(s, result, i);
}
// </vc-code>
