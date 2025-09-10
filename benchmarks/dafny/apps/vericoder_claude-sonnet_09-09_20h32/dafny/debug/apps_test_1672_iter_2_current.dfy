predicate ValidInput(magnets: seq<string>)
{
    forall i :: 0 <= i < |magnets| ==> magnets[i] in {"01", "10"}
}

function CountGroups(magnets: seq<string>) : int
    requires ValidInput(magnets)
{
    if |magnets| == 0 then 0
    else 1 + |set i | 1 <= i < |magnets| && magnets[i] != magnets[i-1]|
}

// <vc-helpers>
lemma CountGroupsNonNegative(magnets: seq<string>)
    requires ValidInput(magnets)
    ensures CountGroups(magnets) >= 0
{
    if |magnets| == 0 {
        assert CountGroups(magnets) == 0;
    } else {
        assert CountGroups(magnets) == 1 + |set i {:trigger} | 1 <= i < |magnets| && magnets[i] != magnets[i-1]|;
        assert |set i {:trigger} | 1 <= i < |magnets| && magnets[i] != magnets[i-1]| >= 0;
    }
}

lemma CountGroupsBound(magnets: seq<string>)
    requires ValidInput(magnets)
    ensures CountGroups(magnets) <= |magnets|
{
    if |magnets| == 0 {
        assert CountGroups(magnets) == 0;
    } else {
        var changes := set i {:trigger} | 1 <= i < |magnets| && magnets[i] != magnets[i-1];
        var indices := set i {:trigger} | 1 <= i < |magnets|;
        assert changes <= indices;
        assert indices == set i {:trigger} | 1 <= i <= |magnets| - 1;
        assert |indices| == |magnets| - 1;
        assert |changes| <= |indices|;
        assert |changes| <= |magnets| - 1;
        assert CountGroups(magnets) == 1 + |changes| <= 1 + (|magnets| - 1) == |magnets|;
    }
}

lemma CountGroupsPositive(magnets: seq<string>)
    requires ValidInput(magnets)
    requires |magnets| > 0
    ensures CountGroups(magnets) >= 1
{
    assert CountGroups(magnets) == 1 + |set i {:trigger} | 1 <= i < |magnets| && magnets[i] != magnets[i-1]|;
    assert |set i {:trigger} | 1 <= i < |magnets| && magnets[i] != magnets[i-1]| >= 0;
}

lemma LoopInvariantMaintained(magnets: seq<string>, i: int, groups: int)
    requires ValidInput(magnets)
    requires 1 <= i < |magnets|
    requires groups == 1 + |set j {:trigger} | 1 <= j < i && magnets[j] != magnets[j-1]|
    ensures (if magnets[i] != magnets[i-1] then groups + 1 else groups) == 1 + |set j {:trigger} | 1 <= j < i + 1 && magnets[j] != magnets[j-1]|
{
    var oldSet := set j {:trigger} | 1 <= j < i && magnets[j] != magnets[j-1];
    var newSet := set j {:trigger} | 1 <= j < i + 1 && magnets[j] != magnets[j-1];
    
    if magnets[i] != magnets[i-1] {
        assert newSet == oldSet + {i};
        assert i !in oldSet;
        assert |newSet| == |oldSet| + 1;
    } else {
        assert newSet == oldSet;
        assert |newSet| == |oldSet|;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(magnets: seq<string>) returns (result: int)
    requires ValidInput(magnets)
    ensures result >= 0
    ensures |magnets| == 0 ==> result == 0
    ensures |magnets| > 0 ==> result >= 1
    ensures result <= |magnets|
    ensures result == CountGroups(magnets)
// </vc-spec>
// <vc-code>
{
    CountGroupsNonNegative(magnets);
    CountGroupsBound(magnets);
    if |magnets| > 0 {
        CountGroupsPositive(magnets);
    }
    
    if |magnets| == 0 {
        result := 0;
    } else {
        var groups := 1;
        var i := 1;
        
        while i < |magnets|
            invariant 1 <= i <= |magnets|
            invariant groups == 1 + |set j {:trigger} | 1 <= j < i && magnets[j] != magnets[j-1]|
            invariant groups >= 1
        {
            LoopInvariantMaintained(magnets, i, groups);
            if magnets[i] != magnets[i-1] {
                groups := groups + 1;
            }
            i := i + 1;
        }
        
        result := groups;
    }
}
// </vc-code>

