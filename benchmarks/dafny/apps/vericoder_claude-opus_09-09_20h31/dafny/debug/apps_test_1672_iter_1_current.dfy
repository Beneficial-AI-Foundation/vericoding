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

lemma CountGroupsBound(magnets: seq<string>)
    requires ValidInput(magnets)
    ensures CountGroups(magnets) <= |magnets|
{
    if |magnets| == 0 {
        // Base case: CountGroups(magnets) == 0 <= 0
    } else {
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
        return;
    }
    
    result := 1;
    var i := 1;
    
    while i < |magnets|
        invariant 1 <= i <= |magnets|
        invariant result == 1 + |set j | 1 <= j < i && magnets[j] != magnets[j-1]|
    {
        if magnets[i] != magnets[i-1] {
            result := result + 1;
        }
        i := i + 1;
    }
    
    assert i == |magnets|;
    assert result == 1 + |set j | 1 <= j < |magnets| && magnets[j] != magnets[j-1]|;
    assert result == CountGroups(magnets);
}
// </vc-code>

