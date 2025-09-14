predicate IsLowercaseLetter(c: char)
{
    'a' <= c <= 'z'
}

predicate AllLowercase(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> IsLowercaseLetter(s[i])
}

predicate ValidOutput(result: string)
{
    result == "A" || result == "a"
}

// <vc-helpers>
function IsAllLowercaseRecursive(s: string, i: int): bool
    requires |s| > 0
    requires -1 <= i < |s|
    ensures IsAllLowercaseRecursive(s, i) <==> (forall k :: 0 <= k <= i ==> IsLowercaseLetter(s[k]))
    decreases i
{
    if i < 0 then
        true
    else if !IsLowercaseLetter(s[i]) then
        false
    else
        IsAllLowercaseRecursive(s, i - 1)
}

function IsAllLowercase(s: string): bool
    ensures IsAllLowercase(s) <==> AllLowercase(s)
{
    if |s| == 0 then
        false
    else
        IsAllLowercaseRecursive(s, |s| - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    ensures ValidOutput(result)
    ensures AllLowercase(input) ==> result == "a"
    ensures (|input| == 0 || !AllLowercase(input)) ==> result == "A"
// </vc-spec>
// <vc-code>
{
    if IsAllLowercase(input) {
        result := "a";
    } else {
        result := "A";
    }
}
// </vc-code>

