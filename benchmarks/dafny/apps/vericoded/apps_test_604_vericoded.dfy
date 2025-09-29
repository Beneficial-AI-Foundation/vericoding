predicate ValidInput(arr: seq<int>) {
    true // No specific constraints on input beyond being a sequence of integers
}

function DistinctNonZeroCount(arr: seq<int>): int {
    |set x | x in arr && x != 0|
}

// <vc-helpers>
lemma SetCardinalityBound(s: set<int>, arr: seq<int>)
    requires s == set x {:trigger x in arr} | x in arr && x != 0
    ensures |s| <= |arr|
{
    if |arr| == 0 {
        assert s == {};
    } else {
        var s' := set x {:trigger x in arr[..|arr|-1]} | x in arr[..|arr|-1] && x != 0;
        SetCardinalityBound(s', arr[..|arr|-1]);
        assert |s'| <= |arr| - 1;
        if arr[|arr|-1] != 0 && arr[|arr|-1] in s' {
            assert s == s';
        } else if arr[|arr|-1] != 0 && arr[|arr|-1] !in s' {
            assert s == s' + {arr[|arr|-1]};
            assert |s| == |s'| + 1;
        } else {
            assert s == s';
        }
    }
}

lemma SetBuildingInvariant(i: int, arr: seq<int>, seen: set<int>)
    requires 0 <= i <= |arr|
    requires seen == set x {:trigger x in arr[..i]} | x in arr[..i] && x != 0
    ensures |seen| <= i
{
    if i == 0 {
        assert arr[..0] == [];
        assert seen == {};
    } else {
        var seen' := set x {:trigger x in arr[..i-1]} | x in arr[..i-1] && x != 0;
        SetBuildingInvariant(i-1, arr, seen');
        assert |seen'| <= i - 1;
        if arr[i-1] != 0 && arr[i-1] !in seen' {
            assert seen == seen' + {arr[i-1]};
            assert |seen| == |seen'| + 1 <= i;
        } else {
            assert seen == seen';
            assert |seen| <= i;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<int>) returns (result: int)
    requires ValidInput(arr)
    ensures result >= 0
    ensures result <= |arr|
    ensures result == DistinctNonZeroCount(arr)
// </vc-spec>
// <vc-code>
{
    var seen: set<int> := {};
    var i := 0;
    
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant seen == set x {:trigger x in arr[..i]} | x in arr[..i] && x != 0
        invariant |seen| <= i
    {
        if arr[i] != 0 {
            seen := seen + {arr[i]};
        }
        assert arr[..i+1] == arr[..i] + [arr[i]];
        i := i + 1;
    }
    
    assert arr[..|arr|] == arr;
    result := |seen|;
}
// </vc-code>

