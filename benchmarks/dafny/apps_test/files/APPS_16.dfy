This verification task involves determining whether four types of 2-character bracket strings can be arranged to form a regular bracket sequence. The algorithm must verify that opening and closing brackets are balanced and that at no point do closing brackets exceed opening brackets when read left to right.

// ======= TASK =======
// Given counts of four types of 2-character bracket strings (cnt1="((", cnt2="()", cnt3=")(", cnt4="))"),
// determine if these strings can be arranged in some order to form a regular bracket sequence
// where at no point do closing brackets exceed opening brackets when read left to right,
// and total opening brackets equal total closing brackets.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(input: string)
{
    var lines := splitFunction(input, '\n');
    |lines| >= 4 && 
    forall i :: 0 <= i < 4 ==> isValidInteger(lines[i])
}

predicate CanFormRegularSequence(cnt1: int, cnt2: int, cnt3: int, cnt4: int)
{
    cnt1 >= 0 && cnt2 >= 0 && cnt3 >= 0 && cnt4 >= 0 &&
    cnt1 == cnt4 && !(cnt3 != 0 && cnt1 == 0)
}

function splitFunction(s: string, delimiter: char): seq<string>
{
    splitHelper(s, delimiter, 0, "")
}

function splitHelper(s: string, delimiter: char, index: int, current: string): seq<string>
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index == |s| then
        if |current| > 0 then [current] else []
    else if s[index] == delimiter then
        [current] + splitHelper(s, delimiter, index + 1, "")
    else
        splitHelper(s, delimiter, index + 1, current + [s[index]])
}

predicate isValidInteger(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
}

function parseIntegerFunction(s: string): int
    requires isValidInteger(s)
    ensures parseIntegerFunction(s) >= 0
{
    parseIntegerHelper(s, 0, 0)
}

function parseIntegerHelper(s: string, index: int, acc: int): int
    requires isValidInteger(s)
    requires 0 <= index <= |s|
    requires acc >= 0
    ensures parseIntegerHelper(s, index, acc) >= 0
    decreases |s| - index
{
    if index == |s| then acc
    else parseIntegerHelper(s, index + 1, acc * 10 + (s[index] as int - '0' as int))
}

// ======= HELPERS =======
method split(s: string, delimiter: char) returns (parts: seq<string>)
    requires |s| >= 0
    ensures parts == splitFunction(s, delimiter)
{
    parts := splitRecursive(s, delimiter, 0, "");
}

method splitRecursive(s: string, delimiter: char, index: int, current: string) returns (parts: seq<string>)
    requires 0 <= index <= |s|
    ensures parts == splitHelper(s, delimiter, index, current)
    decreases |s| - index
{
    if index == |s| {
        if |current| > 0 {
            parts := [current];
        } else {
            parts := [];
        }
    } else if s[index] == delimiter {
        var rest := splitRecursive(s, delimiter, index + 1, "");
        parts := [current] + rest;
    } else {
        parts := splitRecursive(s, delimiter, index + 1, current + [s[index]]);
    }
}

method parseInteger(s: string) returns (n: int)
    requires isValidInteger(s)
    ensures n >= 0
    ensures n == parseIntegerFunction(s)
{
    n := parseIntegerRecursive(s, 0, 0);
}

method parseIntegerRecursive(s: string, index: int, acc: int) returns (result: int)
    requires isValidInteger(s)
    requires 0 <= index <= |s|
    requires acc >= 0
    ensures result == parseIntegerHelper(s, index, acc)
    ensures result >= 0
    decreases |s| - index
{
    if index == |s| {
        result := acc;
    } else {
        result := parseIntegerRecursive(s, index + 1, acc * 10 + (s[index] as int - '0' as int));
    }
}

// <vc-helpers>
// </vc-helpers>

// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures output == "0" || output == "1"
    ensures (
        var lines := splitFunction(input, '\n');
        var cnt1 := parseIntegerFunction(lines[0]);
        var cnt2 := parseIntegerFunction(lines[1]); 
        var cnt3 := parseIntegerFunction(lines[2]);
        var cnt4 := parseIntegerFunction(lines[3]);
        output == "1" <==> CanFormRegularSequence(cnt1, cnt2, cnt3, cnt4)
    )
{
    var lines := split(input, '\n');
    if |lines| < 4 {
        return "0";
    }

    var cnt1 := parseInteger(lines[0]);
    var cnt2 := parseInteger(lines[1]);
    var cnt3 := parseInteger(lines[2]);
    var cnt4 := parseInteger(lines[3]);

    if cnt1 != cnt4 {
        return "0";
    }

    if cnt3 != 0 && cnt1 == 0 {
        return "0";
    }

    return "1";
}
