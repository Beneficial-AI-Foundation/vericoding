predicate ValidInputFormat(input: string)
{
    var trimmed := TrimNewlines(input);
    var spaceIndex := FindSpace(trimmed);
    spaceIndex >= 0 && spaceIndex < |trimmed| - 1 &&
    IsValidInteger(trimmed[..spaceIndex]) &&
    IsValidInteger(trimmed[spaceIndex+1..])
}

predicate ValidInput(input: string, S: int, W: int)
{
    ValidInputFormat(input) &&
    var trimmed := TrimNewlines(input);
    var spaceIndex := FindSpace(trimmed);
    var sStr := trimmed[..spaceIndex];
    var wStr := trimmed[spaceIndex+1..];
    StringToInt(sStr) == S && StringToInt(wStr) == W
}

predicate IsValidInteger(s: string)
{
    if |s| == 0 then false
    else if s[0] == '-' then
        |s| > 1 && forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9'
    else
        forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function TrimNewlines(s: string): string
{
    if |s| == 0 then s
    else if s[|s|-1] == '\n' then TrimNewlines(s[..|s|-1])
    else s
}

function FindSpace(s: string): int
{
    FindSpaceHelper(s, 0)
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' && |s| > 1 then
        -StringToIntHelper(s[1..], 0, 0)
    else
        StringToIntHelper(s, 0, 0)
}

// <vc-helpers>
function FindSpaceHelper(s: string, i: int): int
    requires 0 <= i <= |s|
    ensures -1 <= FindSpaceHelper(s, i) < |s|
    ensures FindSpaceHelper(s, i) >= 0 ==> s[FindSpaceHelper(s, i)] == ' '
    ensures FindSpaceHelper(s, i) >= 0 ==> forall j :: i <= j < FindSpaceHelper(s, i) ==> s[j] != ' '
    decreases |s| - i
{
    if i >= |s| then -1
    else if s[i] == ' ' then i
    else FindSpaceHelper(s, i + 1)
}

function StringToIntHelper(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    requires forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
    requires acc >= 0
    ensures StringToIntHelper(s, i, acc) >= acc
    decreases |s| - i
{
    if i >= |s| then acc
    else StringToIntHelper(s, i + 1, acc * 10 + (s[i] - '0') as int)
}

function StringToIntFixed(s: string): int
    requires IsValidInteger(s)
{
    if |s| == 0 then 0
    else if s[0] == '-' && |s| > 1 then
        -StringToIntHelper(s[1..], 0, 0)
    else
        StringToIntHelper(s, 0, 0)
}

lemma StringToIntHelperWorks(s: string)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures StringToIntHelper(s, 0, 0) >= 0
{
}

lemma SubstringDigits(s: string)
    requires |s| > 1
    requires s[0] == '-'
    requires forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures forall j :: 0 <= j < |s[1..]| ==> '0' <= s[1..][j] <= '9'
{
    assert |s[1..]| == |s| - 1;
    forall j | 0 <= j < |s[1..]|
        ensures '0' <= s[1..][j] <= '9'
    {
        assert s[1..][j] == s[j + 1];
        assert 1 <= j + 1 < |s|;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures result == "safe\n" || result == "unsafe\n" || result == ""
    ensures ValidInputFormat(input) ==> 
        var trimmed := TrimNewlines(input);
        var spaceIndex := FindSpace(trimmed);
        var S := StringToInt(trimmed[..spaceIndex]);
        var W := StringToInt(trimmed[spaceIndex+1..]);
        (W < S ==> result == "safe\n") && (W >= S ==> result == "unsafe\n")
    ensures !ValidInputFormat(input) ==> result == ""
// </vc-spec>
// <vc-code>
{
    if !ValidInputFormat(input) {
        return "";
    }
    
    var trimmed := TrimNewlines(input);
    var spaceIndex := FindSpace(trimmed);
    
    var sStr := trimmed[..spaceIndex];
    var wStr := trimmed[spaceIndex+1..];
    
    assert IsValidInteger(sStr);
    assert IsValidInteger(wStr);
    
    var S := StringToIntFixed(sStr);
    var W := StringToIntFixed(wStr);
    
    if W < S {
        return "safe\n";
    } else {
        return "unsafe\n";
    }
}
// </vc-code>

