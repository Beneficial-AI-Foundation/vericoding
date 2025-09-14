// <vc-preamble>
/* Helper function to count occurrences of a target value in a sequence */
function CountOccurrences(xs: seq<int>, target: int): nat
{
    |set i | 0 <= i < |xs| && xs[i] == target|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added trigger attributes to suppress warnings */
lemma CountOccurrencesProperty(xs: seq<int>, target: int, i: int)
    requires 0 <= i < |xs|
    ensures xs[i] == target ==> i in set j | 0 <= j < |xs| && xs[j] == target
{}

lemma CountOccurrencesNonNegative(xs: seq<int>, target: int)
    ensures CountOccurrences(xs, target) >= 0
{}

lemma SubsetCardinality<T>(A: set<T>, B: set<T>)
    requires A <= B
    ensures |A| <= |B|
{
    if A == {} {
        assert |A| == 0 <= |B|;
    } else if B != {} {
        var x :| x in A;
        assert x in B;
        SubsetCardinality(A - {x}, B - {x});
    }
}

lemma SetCardinalityEqualsSize(xs: seq<int>)
    ensures |set i {:trigger} | 0 <= i < |xs| | == |xs|
{
    var T := set i {:trigger} | 0 <= i < |xs|;
    if |xs| == 0 {
        assert T == {};
        assert |T| == 0;
    } else {
        var s := set i {:trigger} | 0 <= i < |xs| - 1;
        SetCardinalityEqualsSize(xs[..|xs|-1]);
        assert |s| == |xs| - 1;
        assert T == s + {|xs| - 1};
        assert |xs| - 1 !in s;
        assert |T| == |s| + 1;
    }
}

lemma CountOccurrencesUpperBound(xs: seq<int>, target: int)
    ensures CountOccurrences(xs, target) <= |xs|
{
    var S := set i | 0 <= i < |xs| && xs[i] == target;
    var T := set i {:trigger} | 0 <= i < |xs|;
    assert S <= T;
    SetCardinalityEqualsSize(xs);
    assert |T| == |xs|;
    SubsetCardinality(S, T);
}
// </vc-helpers>

// <vc-spec>
method MostFrequent(xs: array<int>) returns (result: int)
    requires xs.Length > 0
    ensures result in xs[..]
    ensures forall x :: x in xs[..] ==> CountOccurrences(xs[..], x) <= CountOccurrences(xs[..], result)
    ensures exists first_idx :: 
        0 <= first_idx < xs.Length && 
        xs[first_idx] == result && 
        CountOccurrences(xs[..], result) == CountOccurrences(xs[..], xs[first_idx]) &&
        forall i :: 0 <= i < first_idx ==> CountOccurrences(xs[..], xs[i]) < CountOccurrences(xs[..], result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes needed to method body */
{
    result := xs[0];
    var maxCount := CountOccurrences(xs[..], result);
    var i := 1;
    
    while i < xs.Length
        invariant 1 <= i <= xs.Length
        invariant result in xs[..]
        invariant maxCount == CountOccurrences(xs[..], result)
        invariant forall j :: 0 <= j < i ==> CountOccurrences(xs[..], xs[j]) <= maxCount
        invariant exists first_idx :: (0 <= first_idx < i && xs[first_idx] == result && 
                  forall k :: 0 <= k < first_idx ==> CountOccurrences(xs[..], xs[k]) < maxCount)
    {
        var currentCount := CountOccurrences(xs[..], xs[i]);
        if currentCount > maxCount {
            result := xs[i];
            maxCount := currentCount;
        }
        i := i + 1;
    }
}
// </vc-code>
