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

function PrefixSet(names: seq<string>, i: int): set<string>
    requires 0 <= i <= |names|
    decreases i
{
    if i == 0 then {}
    else PrefixSet(names, i-1) + {names[i-1]}
}
// </vc-helpers>

// <vc-spec>
method solve(names: seq<string>) returns (output: seq<string>)
    ensures ValidOutput(names, output)
// </vc-spec>
// <vc-code>
{
    var n := |names|;
    var arr := new string[n];
    var seen := {};
    
    for i := 0 to n
        invariant 0 <= i <= n
        invariant |arr| == n
        invariant seen == PrefixSet(names, i)
        invariant forall j :: 0 <= j < i ==> 
            arr[j] == (if HasSeenBefore(names, j) then "YES" else "NO")
    {
        if i < n {
            var name := names[i];
            arr[i] := if name in seen then "YES" else "NO";
            seen := seen + {name};
        }
    }
    output := arr[..];
}
// </vc-code>

