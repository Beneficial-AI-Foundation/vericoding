predicate ValidOutput(names: seq<string>, output: seq<string>)
{
    |output| == |names| &&
    forall i :: 0 <= i < |names| ==> 
        output[i] == (if exists j :: 0 <= j < i && names[j] == names[i] then "YES" else "NO")
}

// <vc-helpers>
function HasSeenBefore(names: seq<string>, i: int): bool
    requires 0 <= i < |names|
{
    exists j :: 0 <= j < i && names[j] == names[i]
}
// </vc-helpers>

// <vc-spec>
method solve(names: seq<string>) returns (output: seq<string>)
    ensures ValidOutput(names, output)
// </vc-spec>
// <vc-code>
{
    var n := |names|;
    output := new string[n];
    var seen := new set<string>;
    
    for i := 0 to n
        invariant 0 <= i <= n
        invariant |output| == n
        invariant seen == set names[0..i]
        invariant forall j :: 0 <= j < i ==> 
            output[j] == (if HasSeenBefore(names, j) then "YES" else "NO")
    {
        if i < n {
            var name := names[i];
            output[i] := if name in seen then "YES" else "NO";
            seen := seen + {name};
        }
    }
}
// </vc-code>

