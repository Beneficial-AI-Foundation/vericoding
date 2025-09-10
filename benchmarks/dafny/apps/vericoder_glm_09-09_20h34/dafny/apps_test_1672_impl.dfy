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
lemma Lemma_CountGroups_Properties(magnets: seq<string>)
    requires ValidInput(magnets)
    ensures CountGroups(magnets) >= 0
    ensures |magnets| == 0 ==> CountGroups(magnets) == 0
    ensures |magnets| > 0 ==> CountGroups(magnets) >= 1
    ensures CountGroups(magnets) <= |magnets|
{
    if |magnets| == 0 {
        assert CountGroups(magnets) == 0;
    } else {
        var n := |magnets|;
        var indices := { j | 1 <= j < n };
        assert |indices| == n - 1;
        var S := { j | 1 <= j < n && magnets[j] != magnets[j-1] };
        assert S <= indices;
        assert |S| <= |indices|;
        assert CountGroups(magnets) == 1 + |S|;
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
    Lemma_CountGroups_Properties(magnets);
    return CountGroups(magnets);
}
// </vc-code>

