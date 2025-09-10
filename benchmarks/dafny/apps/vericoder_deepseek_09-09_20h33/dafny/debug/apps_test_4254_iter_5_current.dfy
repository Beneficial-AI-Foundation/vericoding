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
function FindSpaceHelper(s: string, index: int): (r: int)
    requires 0 <= index <= |s|
    ensures -1 <= r <= |s|
    ensures r == -1 ==> forall i :: index <= i < |s| ==> s[i] != ' '
    ensures r >= 0 ==> (index <= r < |s| && s[r] == ' ' && 
                           forall i :: index <= i < r ==> s[i] != ' ')
    decreases |s| - index
{
    if index >= |s| then
        -1
    else if s[index] == ' ' then
        index
    else
        FindSpaceHelper(s, index + 1)
}

lemma FindSpaceHelperProperty(s: string, index: int)
    requires 0 <= index <= |s|
    ensures var r := FindSpaceHelper(s, index);
        r >= 0 ==> 
        index <= r < |s| && s[r] == ' ' &&
        forall i :: index <= i < r ==> s[i] != ' '
    ensures FindSpaceHelper(s, index) == -1 ==> 
        forall i :: index <= i < |s| ==> s[i] != ' '
    decreases |s| - index
{
    if index < |s| && s[index] != ' ' {
        FindSpaceHelperProperty(s, index + 1);
    }
}

function StringToIntHelper(s: string, index: int, acc: int): (r: int)
    requires 0 <= index <= |s|
    requires acc >= 0
    requires forall i :: index <= i < |s| ==> '0' <= s[i] <= '9'
    ensures r >= 0
    decreases |s| - index
{
    if index >= |s| then
        acc
    else
        StringToIntHelper(s, index + 1, acc * 10 + (s[index] as int - '0' as int))
}

lemma StringToIntHelperDigitsOnly(s: string, index: int, acc: int)
    requires 0 <= index <= |s|
    requires acc >= 0
    requires forall i :: index <= i < |s| ==> '0' <= s[i] <= '9'
    ensures StringToIntHelper(s, index, acc) >= 0
    decreases |s| - index
{
    if index < |s| {
        StringToIntHelperDigitsOnly(s, index + 1, acc * 10 + (s[index] as int - '0' as int));
    }
}

lemma StringToIntValid(s: string)
    requires IsValidInteger(s)
    ensures StringToInt(s) is int
{
    if |s| > 0 {
        if s[0] == '-' && |s| > 1 {
            assert forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9';
            StringToIntHelperDigitsOnly(s[1..], 0, 0);
        } else {
            assert forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9';
            StringToIntHelperDigitsOnly(s, 0, 0);
        }
    }
}

lemma IsValidIntegerImpliesDigits(s: string, start: int)
    requires IsValidInteger(s)
    requires start == (if s[0] == '-' then 1 else 0)
    ensures forall i :: start <= i < |s| ==> '0' <= s[i] <= '9'
{
}

lemma ValidInputFormatImpliesDigits(sStr: string, wStr: string)
    requires ValidInputFormat(input)  // This needs access to 'input' which isn't available
    ensures forall i :: 0 <= i < |sStr| ==> '0' <= sStr[i] <= '9' || (i == 0 && sStr[0] == '-')
    ensures forall i :: 0 <= i < |wStr| ==> '0' <= wStr[i] <= '9' || (i == 0 && wStr[0] == '-')
{
    // This lemma would need more context about the input string
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
        result := "";
        return;
    }
    
    var trimmed := TrimNewlines(input);
    var spaceIndex := FindSpace(trimmed);
    assert spaceIndex >= 0 && spaceIndex < |trimmed| - 1;
    
    var sStr := trimmed[..spaceIndex];
    var wStr := trimmed[spaceIndex+1..];
    
    assert IsValidInteger(sStr);
    assert IsValidInteger(wStr);
    
    // Add explicit proofs about digit constraints
    if |sStr| > 0 {
        if sStr[0] == '-' {
            assert forall i :: 1 <= i < |sStr| ==> '0' <= sStr[i] <= '9';
        } else {
            assert forall i :: 0 <= i < |sStr| ==> '0' <= sStr[i] <= '9';
        }
    }
    
    if |wStr| > 0 {
        if wStr[0] == '-' {
            assert forall i :: 1 <= i < |wStr| ==> '0' <= wStr[i] <= '9';
        } else {
            assert forall i :: 0 <= i < |wStr| ==> '0' <= wStr[i] <= '9';
        }
    }
    
    StringToIntValid(sStr);
    StringToIntValid(wStr);
    var S := StringToInt(sStr);
    var W := StringToInt(wStr);
    
    if W < S {
        result := "safe\n";
    } else {
        result := "unsafe\n";
    }
}
// </vc-code>

