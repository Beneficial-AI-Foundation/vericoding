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
    decreases |s| - index
    ensures FindSpaceHelper(s, index) >= -1
    ensures FindSpaceHelper(s, index) <= |s| // Changed upper bound to |s| instead of |s|-1
{
    if index >= |s| then -1
    else if s[index] == ' ' then index
    else FindSpaceHelper(s, index + 1)
}

function StringToIntHelper(s: string, index: int, acc: int): int
    decreases |s| - index
    requires index <= |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' // Changed to start from 0 instead of `index`
    // added a check to ensure acc * 10 + (s[index] - '0') does not overflow int
    requires (index < |s| && (acc <= (0x7FFFFFFF - (s[index] - '0')) / 10)) || index == |s|
    ensures StringToIntHelper(s, index, acc) >= 0
{
    if index == |s| then acc
    else
        var digit := (s[index] - '0');
        StringToIntHelper(s, index + 1, acc * 10 + digit)
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
    if !ValidInputFormat(input)
    {
        return "";
    }
    var trimmed := TrimNewlines(input);
    var spaceIndex := FindSpace(trimmed);
    var sStr := trimmed[..spaceIndex];
    var wStr := trimmed[spaceIndex+1..];
    // Add assertions to help Dafny with string slicing preconditions
    // sStr must be a valid integer string.
    assert IsValidInteger(sStr);
    var S := StringToInt(sStr);
    
    // wStr must be a valid integer string.
    assert IsValidInteger(wStr);
    var W := StringToInt(wStr);
    
    if W < S then
        return "safe\n";
    else
        return "unsafe\n";
}
// </vc-code>

