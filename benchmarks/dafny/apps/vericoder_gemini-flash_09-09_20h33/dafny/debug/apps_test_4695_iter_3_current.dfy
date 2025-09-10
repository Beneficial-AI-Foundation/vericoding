predicate ValidInput(input: string)
    requires |input| > 0
{
    var parts := SplitStringPure(input);
    |parts| >= 2 && IsValidInt(parts[0]) && IsValidInt(parts[1])
}

predicate SameGroup(a: int, b: int)
{
    var n1 := [1, 3, 5, 7, 8, 10, 12];
    var n2 := [4, 6, 9, 11];
    (a in n1 && b in n1) || (a in n2 && b in n2) || (a == 2 && b == 2)
}

predicate CorrectOutput(input: string, result: string)
    requires |input| > 0
{
    if ValidInput(input) then
        var parts := SplitStringPure(input);
        var a := StringToIntPure(parts[0]);
        var b := StringToIntPure(parts[1]);
        (result == "Yes\n" <==> SameGroup(a, b)) && (result == "No\n" <==> !SameGroup(a, b))
    else
        result == ""
}

// <vc-helpers>
function SplitStringPure(s: string) : seq<string>
    reads s
    requires |s| > 0
    ensures forall i :: 0 <= i < |SplitStringPure(s)| ==> |SplitStringPure(s)[i]| > 0
{
    var parts: seq<string> := [];
    var start := 0;
    for i := 0 to |s|
        // Loop invariants
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < |parts| ==> |parts[j]| > 0
        invariant 0 <= start <= i
        invariant (i == 0 ==> start == 0)
        invariant (i > 0 && s[i-1] == '-' ==> start == i)
    {
        if i == |s| || s[i] == '-' then
            if i > start then
                parts := parts + [s[start..i]];
            start := i + 1;
        }
    return parts
}

function StringToIntPure(s: string) : int
    reads s
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    var res := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant res == (if i == 0 then 0 else StringToIntPure(s[..i]))
        invariant forall j :: 0 <= j < i ==> '0' <= s[j] <= '9'
    {
        res := res * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    return res
}

predicate IsValidInt(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures result == "Yes\n" || result == "No\n" || result == ""
    ensures CorrectOutput(input, result)
// </vc-spec>
// <vc-code>
{
    if !ValidInput(input) then
        return "";
    var parts := SplitStringPure(input);
    var a := StringToIntPure(parts[0]);
    var b := StringToIntPure(parts[1]);
    if SameGroup(a, b) then
        return "Yes\n";
    else
        return "No\n";
}
// </vc-code>

