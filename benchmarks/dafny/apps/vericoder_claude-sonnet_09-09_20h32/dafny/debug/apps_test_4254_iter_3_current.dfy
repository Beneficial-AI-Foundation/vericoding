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
function FindSpaceHelper(s: string, index: int): int
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index >= |s| then -1
    else if s[index] == ' ' then index
    else FindSpaceHelper(s, index + 1)
}

function StringToIntHelper(s: string, index: int, acc: int): int
    requires 0 <= index <= |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    decreases |s| - index
{
    if index >= |s| then acc
    else 
        var digit := s[index] as int - '0' as int;
        StringToIntHelper(s, index + 1, acc * 10 + digit)
}

lemma NegativeStringDigitsLemma(s: string)
    requires |s| > 1 && s[0] == '-'
    requires forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures forall i :: 0 <= i < |s[1..]| ==> '0' <= s[1..][i] <= '9'
{
    forall i | 0 <= i < |s[1..]|
        ensures '0' <= s[1..][i] <= '9'
    {
        assert s[1..][i] == s[i + 1];
        assert 1 <= i + 1 < |s|;
    }
}

lemma PositiveStringDigitsLemma(s: string)
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
}

lemma ValidStringImpliesDigits(s: string)
    requires IsValidInteger(s)
    ensures if |s| > 0 && s[0] == '-' then
        forall i :: 0 <= i < |s[1..]| ==> '0' <= s[1..][i] <= '9'
    else
        forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| > 0 && s[0] == '-' {
        NegativeStringDigitsLemma(s);
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
    
    ValidStringImpliesDigits(sStr);
    ValidStringImpliesDigits(wStr);
    
    var S := StringToInt(sStr);
    var W := StringToInt(wStr);
    
    if W < S {
        return "safe\n";
    } else {
        return "unsafe\n";
    }
}
// </vc-code>

