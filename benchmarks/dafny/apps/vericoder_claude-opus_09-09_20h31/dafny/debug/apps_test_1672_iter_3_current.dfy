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

lemma SetCardinalityBound(n: int)
    requires n > 0
    ensures |set i | 1 <= i < n| == n - 1
{
    var s := set i | 1 <= i < n;
    assert s == set i | i in {1..n-1};
    assert |{1..n-1}| == n - 1;
}

lemma SubsetCardinalityBound<T>(subset: set<T>, superset: set<T>)
    requires subset <= superset
    ensures |subset| <= |superset|
{
    // This is a fundamental property of finite sets in Dafny
}

lemma SetBoundHelper(magnets: seq<string>, n: int)
    requires ValidInput(magnets)
    requires 0 < n <= |magnets|
    ensures |set i | 1 <= i < n && magnets[i] != magnets[i-1]| <= n - 1
{
    var transitions := set i | 1 <= i < n && magnets[i] != magnets[i-1];
    var indices := set i | 1 <= i < n;
    
    assert transitions <= indices;
    SubsetCardinalityBound(transitions, indices);
    assert |transitions| <= |indices|;
    
    SetCardinalityBound(n);
    assert |indices| == n - 1;
    assert |transitions| <= n - 1;
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
        SetBoundHelper(magnets, i);
        assert |transitions| <= i - 1;
        assert result == 1 + |transitions| <= 1 + (i - 1) == i;
    }
    
    assert i == |magnets|;
    assert transitions == set j | 1 <= j < |magnets| && magnets[j] != magnets[j-1];
    assert result == 1 + |transitions|;
    assert result == CountGroups(magnets);
    CountGroupsBound(magnets);
}
// </vc-code>

