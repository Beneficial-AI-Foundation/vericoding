// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
    var seen: set<int> := {};
    result := [];

    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        invariant forall k: int :: 0 <= k < i ==> seen contains s[k]
        invariant forall k: int :: 0 <= k < |result| ==> seen contains result[k]
        invariant forall k: int :: 0 <= k < |result| ==> (exists m: int :: 0 <= m < i && s[m] == result[k])
        invariant forall k: int, l: int :: 0 <= k < l < |result| ==> result[k] != result[l]
    {
        if !(seen contains s[i])
        {
            result := result + [s[i]];
            seen := seen + {s[i]};
        }
    }
}
// </vc-code>
