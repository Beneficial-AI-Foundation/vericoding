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
    {
        if magnets[i] != magnets[i-1] {
            result := result + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

