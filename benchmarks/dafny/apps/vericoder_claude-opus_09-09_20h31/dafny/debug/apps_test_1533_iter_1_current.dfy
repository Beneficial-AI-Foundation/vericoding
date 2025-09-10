predicate ValidOutput(names: seq<string>, output: seq<string>)
{
    |output| == |names| &&
    forall i :: 0 <= i < |names| ==> 
        output[i] == (if exists j :: 0 <= j < i && names[j] == names[i] then "YES" else "NO")
}

// <vc-helpers>
lemma ValidOutputPrefix(names: seq<string>, output: seq<string>, k: int)
    requires 0 <= k <= |names|
    requires |output| == k
    requires forall i :: 0 <= i < k ==> 
        output[i] == (if exists j :: 0 <= j < i && names[j] == names[i] then "YES" else "NO")
    ensures ValidOutput(names[..k], output)
{
    assert |output| == |names[..k]|;
    assert forall i :: 0 <= i < |names[..k]| ==>
        output[i] == (if exists j :: 0 <= j < i && names[..k][j] == names[..k][i] then "YES" else "NO");
}
// </vc-helpers>

// <vc-spec>
method solve(names: seq<string>) returns (output: seq<string>)
    ensures ValidOutput(names, output)
// </vc-spec>
// <vc-code>
{
    output := [];
    var k := 0;
    
    while k < |names|
        invariant 0 <= k <= |names|
        invariant |output| == k
        invariant forall i :: 0 <= i < k ==> 
            output[i] == (if exists j :: 0 <= j < i && names[j] == names[i] then "YES" else "NO")
    {
        var found := false;
        var j := 0;
        
        while j < k
            invariant 0 <= j <= k
            invariant found == (exists m :: 0 <= m < j && names[m] == names[k])
        {
            if names[j] == names[k] {
                found := true;
                break;
            }
            j := j + 1;
        }
        
        if found {
            output := output + ["YES"];
        } else {
            output := output + ["NO"];
        }
        
        k := k + 1;
    }
}
// </vc-code>

