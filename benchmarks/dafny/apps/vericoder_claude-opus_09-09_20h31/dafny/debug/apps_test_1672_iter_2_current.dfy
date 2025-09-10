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
lemma CountGroupsBase(magnets: seq<string>)
    requires ValidInput(magnets)
    requires |magnets| == 0
    ensures CountGroups(magnets) == 0
{
    // Trivially true by definition
}

lemma CountGroupsSingle(magnets: seq<string>)
    requires ValidInput(magnets)
    requires |magnets| == 1
    ensures CountGroups(magnets) == 1
{
    assert |set i | 1 <= i < |magnets| && magnets[i] != magnets[i-1]| == 0;
}

lemma SetBoundHelper(magnets: seq<string>, n: int)
    requires ValidInput(magnets)
    requires 0 < n <= |magnets|
    ensures |set i | 1 <= i < n && magnets[i] != magnets[i-1]| <= n - 1
{
    var s := set i | 1 <= i < n && magnets[i] != magnets[i-1];
    assert s <= set i | 1 <= i < n;
    assert |set i | 1 <= i < n| == n - 1;
}

lemma CountGroupsBound(magnets: seq<string>)
    requires ValidInput(magnets)
    ensures CountGroups(magnets) <= |magnets|
{
    if |magnets| == 0 {
        // Base case: CountGroups(magnets) == 0 <= 0
    } else {
        SetBoundHelper(magnets, |magnets|);
        var s := set i | 1 <= i < |magnets| && magnets[i] != magnets[i-1];
        assert |s| <= |magnets| - 1;
        assert CountGroups(magnets) == 1 + |s| <= 1 + |magnets| - 1 == |magnets|;
    }
}

lemma CountGroupsIterative(magnets: seq<string>, k: int)
    requires ValidInput(magnets)
    requires 0 <= k <= |magnets|
    ensures CountGroups(magnets[..k]) == 
        if k == 0 then 0
        else 1 + |set i | 1 <= i < k && magnets[i] != magnets[i-1]|
{
    if k == 0 {
        assert magnets[..k] == [];
    } else {
        assert magnets[..k] == magnets[..k];
        assert forall i :: 0 <= i < k ==> magnets[..k][i] == magnets[i];
    }
}

lemma LoopInvariantHelper(magnets: seq<string>, i: int, result: int)
    requires ValidInput(magnets)
    requires 1 <= i <= |magnets|
    requires result >= 1
    ensures result <= i
{
    // The number of groups can't exceed the number of elements seen
    if result > i {
        // This would mean we have more transitions than positions
        assert false;
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
    if |magnets| == 0 {
        result := 0;
        CountGroupsBase(magnets);
        return;
    }
    
    result := 1;
    var i := 1;
    var transitions := set j | 1 <= j < i && magnets[j] != magnets[j-1];
    assert transitions == {};
    assert |transitions| == 0;
    
    while i < |magnets|
        invariant 1 <= i <= |magnets|
        invariant transitions == set j | 1 <= j < i && magnets[j] != magnets[j-1]
        invariant result == 1 + |transitions|
        invariant result >= 1
        invariant result <= i
    {
        var old_transitions := transitions;
        transitions := set j | 1 <= j < i + 1 && magnets[j] != magnets[j-1];
        
        if magnets[i] != magnets[i-1] {
            assert i in transitions;
            assert i !in old_transitions;
            assert transitions == old_transitions + {i};
            result := result + 1;
        } else {
            assert transitions == old_transitions;
        }
        
        i := i + 1;
        assert result <= i;
    }
    
    assert i == |magnets|;
    assert transitions == set j | 1 <= j < |magnets| && magnets[j] != magnets[j-1];
    assert result == 1 + |transitions|;
    assert result == CountGroups(magnets);
    CountGroupsBound(magnets);
}
// </vc-code>

