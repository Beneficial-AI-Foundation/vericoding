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
lemma CountGroupsLemma(magnets: seq<string>)
    requires ValidInput(magnets)
    ensures |magnets| > 0 ==> CountGroups(magnets) == 1 + (|set i | 1 <= i < |magnets| && magnets[i] != magnets[i-1]|)
{
    // Built-in to help verification
}

lemma CountGroupsSliceLemma(magnets: seq<string>, i: int)
    requires ValidInput(magnets)
    requires 0 <= i <= |magnets|
    ensures CountGroups(magnets[0..i]) >= 1 || i == 0
    decreases i
{
    if i == 0 {
        // Base case: empty sequence
    } else if i == 1 {
        // Single element: exactly 1 group
    } else {
        // Recursive case: compare with smaller slice
        CountGroupsSliceLemma(magnets, i-1);
    }
}

lemma CountGroupsMonotonic(magnets: seq<string>, i: int, j: int)
    requires ValidInput(magnets)
    requires 0 <= i <= j <= |magnets|
    ensures CountGroups(magnets[0..i]) <= CountGroups(magnets[0..j])
{
    if i < j {
        var slice := magnets[0..j];
        var prev_slice := magnets[0..i];
        CountGroupsSliceLemma(magnets, i);
        CountGroupsSliceLemma(magnets, j);
        
        if j == i + 1 {
            // Adding one element: the count stays the same or increases by 1
            if i > 0 && magnets[i-1] != magnets[i] {
                // Groups increase
                assert CountGroups(magnets[0..j]) == CountGroups(prev_slice) + 1;
            } else {
                // Groups stay the same
                assert CountGroups(magnets[0..j]) == CountGroups(prev_slice);
            }
        } else {
            // General case: use induction
            CountGroupsMonotonic(magnets, i, j-1);
            CountGroupsMonotonic(magnets, j-1, j);
            assert CountGroups(magnets[0..i]) <= CountGroups(magnets[0..j-1]) <= CountGroups(magnets[0..j]);
        }
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
        invariant result == CountGroups(magnets[0..i])
        invariant result >= 1
        invariant result <= i
    {
        if magnets[i] != magnets[i-1] {
            result := result + 1;
        }
        CountGroupsMonotonic(magnets, i, i+1);
        i := i + 1;
    }
    
    // Final verification that we've processed the entire sequence
    assert i == |magnets|;
    assert magnets[0..i] == magnets;
}
// </vc-code>

