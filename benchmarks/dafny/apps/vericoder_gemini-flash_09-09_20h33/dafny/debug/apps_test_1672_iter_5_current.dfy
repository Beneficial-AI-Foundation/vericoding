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
        assert 1 + (|set i | 1 <= i < |magnets| && magnets[i] != magnets[i-1]|) >= 1;
        assert CountGroups(magnets) >= 1;
    }
}

lemma CountGroupsUpperBound(magnets: seq<string>)
    requires ValidInput(magnets)
    ensures CountGroups(magnets) <= |magnets|
{
    if |magnets| == 0 {
        assert CountGroups(magnets) == 0;
    } else {
        var num_different := |set i | 1 <= i < |magnets| && magnets[i] != magnets[i-1]|;
        // The maximum value for num_different is |magnets| - 1, because i starts from 1 and goes up to |magnets|-1.
        // There are |magnets|-1 possible adjacent pairs.
        assert num_different <= |magnets| - 1; 
        assert CountGroups(magnets) == 1 + num_different;
        assert CountGroups(magnets) <= 1 + (|magnets| - 1);
        assert CountGroups(magnets) <= |magnets|;
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
    // These lemmas are crucial for the postconditions. The verifier uses them to reason about the correct ranges.
    CountGroupsNonNegative(magnets);
    CountGroupsUpperBound(magnets);
    
    if |magnets| == 0 {
        result := 0;
    } else {
        var groups := 1;
        var i := 1;
        while i < |magnets|
            invariant 1 <= i <= |magnets|
            invariant groups == 1 + |set j | 1 <= j < i && magnets[j] != magnets[j-1]|
            invariant 1 <= groups
            invariant groups <= i + 1 // Added invariant
            invariant ValidInput(magnets)
            decreases |magnets| - i
        {
            if magnets[i] != magnets[i-1] {
                groups := groups + 1;
            }
            i := i + 1;
        }
        result := groups;
        assert result == CountGroups(magnets); // Added assertion to prove postcondition
    }
}
// </vc-code>

