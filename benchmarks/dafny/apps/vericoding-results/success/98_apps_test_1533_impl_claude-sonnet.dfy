predicate ValidOutput(names: seq<string>, output: seq<string>)
{
    |output| == |names| &&
    forall i :: 0 <= i < |names| ==> 
        output[i] == (if exists j :: 0 <= j < i && names[j] == names[i] then "YES" else "NO")
}

// <vc-helpers>
lemma ExistenceEquivalence(names: seq<string>, i: int)
    requires 0 <= i < |names|
    ensures (exists j :: 0 <= j < i && names[j] == names[i]) <==> (names[i] in names[..i])
{
    if exists j :: 0 <= j < i && names[j] == names[i] {
        var j :| 0 <= j < i && names[j] == names[i];
        assert names[j] in names[..i];
        assert names[i] == names[j];
        assert names[i] in names[..i];
    }
    
    if names[i] in names[..i] {
        var k :| 0 <= k < i && names[..i][k] == names[i];
        assert names[k] == names[i];
        assert exists j :: 0 <= j < i && names[j] == names[i];
    }
}
// </vc-helpers>

// <vc-spec>
method solve(names: seq<string>) returns (output: seq<string>)
    ensures ValidOutput(names, output)
// </vc-spec>
// <vc-code>
{
    output := [];
    
    for i := 0 to |names|
        invariant |output| == i
        invariant forall k :: 0 <= k < i ==> 
            output[k] == (if exists j :: 0 <= j < k && names[j] == names[k] then "YES" else "NO")
    {
        ExistenceEquivalence(names, i);
        
        if names[i] in names[..i] {
            output := output + ["YES"];
        } else {
            output := output + ["NO"];
        }
    }
}
// </vc-code>

