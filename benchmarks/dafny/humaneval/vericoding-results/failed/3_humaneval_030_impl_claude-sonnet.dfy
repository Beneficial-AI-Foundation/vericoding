// <vc-preamble>

predicate IsPositive(x: int)
{
    x > 0
}

predicate AllPositive(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> IsPositive(s[i])
}

predicate AllElementsFromOriginal(result: seq<int>, original: seq<int>)
{
    forall x :: x in result ==> x in original
}

predicate ContainsAllPositives(result: seq<int>, original: seq<int>)
{
    forall i :: 0 <= i < |original| && IsPositive(original[i]) ==> original[i] in result
}

predicate PreservesOrder(result: seq<int>, original: seq<int>)
{
    forall i, j :: 0 <= i < j < |result| ==> 
        (exists k1, k2 :: (0 <= k1 < k2 < |original| && original[k1] == result[i] && original[k2] == result[j] &&
        forall k :: k1 < k < k2 ==> !IsPositive(original[k])))
}

function CountPositives(s: seq<int>): int
{
    |set x | x in s && IsPositive(x)|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Simplified lemma to handle the exact expression pattern and added counting lemma */
lemma CountPositivesExtension(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures CountPositives(s[..i+1]) == CountPositives(s[..i]) + (if IsPositive(s[i]) then 1 else 0)
{
    var s1 := s[..i];
    var s2 := s[..i+1];
    assert s2 == s1 + [s[i]];
    
    if IsPositive(s[i]) {
        assert s[i] in s2;
        assert IsPositive(s[i]);
    }
}

lemma CountPositivesInResult(l: seq<int>, result: seq<int>)
    requires forall x :: x in result ==> x in l && IsPositive(x)
    requires forall j :: 0 <= j < |l| && IsPositive(l[j]) ==> l[j] in result
    ensures |result| == CountPositives(l)
{
    var pos_l := set x | x in l && IsPositive(x);
    var pos_result := set x | x in result;
    
    // All elements in result are positive and from l
    assert forall x :: x in pos_result ==> x in pos_l;
    
    // All positive elements from l are in result
    assert forall x :: x in pos_l ==> x in pos_result;
    
    // Therefore the sets are equal
    assert pos_result == pos_l;
    assert |pos_result| == |pos_l|;
    assert |result| >= |pos_result|;
}

lemma OrderPreservationHelper(result: seq<int>, l: seq<int>, indices: seq<int>)
    requires |result| == |indices|
    requires forall k :: 0 <= k < |indices| ==> 0 <= indices[k] < |l|
    requires forall k :: 0 <= k < |result| ==> result[k] == l[indices[k]]
    requires forall k1, k2 :: 0 <= k1 < k2 < |indices| ==> indices[k1] < indices[k2]
    ensures PreservesOrder(result, l)
{
    // The indices are strictly increasing, so order is preserved
}
// </vc-helpers>

// <vc-spec>
method get_positive(l: seq<int>) returns (result: seq<int>)
    ensures AllPositive(result)
    ensures AllElementsFromOriginal(result, l)
    ensures ContainsAllPositives(result, l)
    ensures |result| == CountPositives(l)
    ensures PreservesOrder(result, l)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added explicit index tracking and lemma calls */
    result := [];
    var i := 0;
    var indices := [];
    
    while i < |l|
        invariant 0 <= i <= |l|
        invariant |result| == |indices|
        invariant forall j :: 0 <= j < |result| ==> IsPositive(result[j])
        invariant forall x :: x in result ==> x in l
        invariant forall j :: 0 <= j < i && IsPositive(l[j]) ==> l[j] in result
        invariant forall k :: 0 <= k < |indices| ==> 0 <= indices[k] < |l|
        invariant forall k :: 0 <= k < |result| ==> result[k] == l[indices[k]]
        invariant forall k1, k2 :: 0 <= k1 < k2 < |indices| ==> indices[k1] < indices[k2]
    {
        if l[i] > 0 {
            result := result + [l[i]];
            indices := indices + [i];
        }
        i := i + 1;
    }
    
    // Call helper lemmas to establish postconditions
    CountPositivesInResult(l, result);
    OrderPreservationHelper(result, l, indices);
}
// </vc-code>
