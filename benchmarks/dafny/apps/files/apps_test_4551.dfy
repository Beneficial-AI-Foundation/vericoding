Given four integer weights A, B, C, D, determine the direction a balance scale tips when:
- Left pan contains masses with weights A and B  
- Right pan contains masses with weights C and D
Compare the total weights on each side and output "Left", "Right", or "Balanced"

predicate ValidParseable(input: string)
{
    var parts := SplitStringPure(input);
    |parts| >= 4
}

predicate AllPartsAreIntegers(input: string)
{
    var parts := SplitStringPure(input);
    |parts| >= 4 &&
    IsValidInteger(parts[0]) &&
    IsValidInteger(parts[1]) &&
    IsValidInteger(parts[2]) &&
    IsValidInteger(parts[3])
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> ('0' <= s[i] <= '9') || (i == 0 && s[i] == '-'))
}

predicate ValidParse(input: string, a: int, b: int, c: int, d: int)
{
    var parts := SplitStringPure(input);
    |parts| >= 4 && 
    IsValidInteger(parts[0]) &&
    IsValidInteger(parts[1]) &&
    IsValidInteger(parts[2]) &&
    IsValidInteger(parts[3]) &&
    StringToIntPure(parts[0]) == a &&
    StringToIntPure(parts[1]) == b &&
    StringToIntPure(parts[2]) == c &&
    StringToIntPure(parts[3]) == d
}

function SplitStringPure(s: string): seq<string>
{
    SplitStringHelper(s, 0, "", [])
}

function SplitStringHelper(s: string, i: int, current: string, acc: seq<string>): seq<string>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        if |current| > 0 then acc + [current] else acc
    else if s[i] == ' ' || s[i] == '\n' || s[i] == '\t' then
        if |current| > 0 then
            SplitStringHelper(s, i + 1, "", acc + [current])
        else
            SplitStringHelper(s, i + 1, "", acc)
    else
        SplitStringHelper(s, i + 1, current + [s[i]], acc)
}

function StringToIntPure(s: string): int
    requires IsValidInteger(s)
{
    if |s| > 0 && s[0] == '-' then
        -StringToIntHelperUnsigned(s, 1, 0)
    else
        StringToIntHelperUnsigned(s, 0, 0)
}

function StringToIntHelperUnsigned(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i == |s| then acc
    else if '0' <= s[i] <= '9' then
        StringToIntHelperUnsigned(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    else
        acc
}

predicate AllPartsValidIntegers(parts: seq<string>)
{
    |parts| >= 4 &&
    IsValidInteger(parts[0]) &&
    IsValidInteger(parts[1]) &&
    IsValidInteger(parts[2]) &&
    IsValidInteger(parts[3])
}

method SplitString(s: string) returns (parts: seq<string>)
    requires |s| >= 0
    ensures |parts| >= 0
    ensures forall i :: 0 <= i < |parts| ==> |parts[i]| > 0
    ensures parts == SplitStringPure(s)
{
    parts := [];
    var current := "";
    var i := 0;

    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < |parts| ==> |parts[j]| > 0
        invariant SplitStringHelper(s, i, current, parts) == SplitStringHelper(s, 0, "", [])
    {
        if s[i] == ' ' || s[i] == '\n' || s[i] == '\t' {
            if |current| > 0 {
                parts := parts + [current];
                current := "";
            }
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }

    if |current| > 0 {
        parts := parts + [current];
    }
}

method StringToInt(s: string) returns (n: int)
    requires |s| >= 0
    requires IsValidInteger(s)
    ensures n == StringToIntPure(s)
{
    if |s| == 0 {
        n := 0;
        return;
    }

    var start := 0;
    var negative := false;

    if s[0] == '-' {
        negative := true;
        start := 1;
    }

    n := 0;
    var i := start;
    while i < |s|
        invariant start <= i <= |s|
        invariant StringToIntHelperUnsigned(s, i, n) == StringToIntHelperUnsigned(s, start, 0)
    {
        if '0' <= s[i] <= '9' {
            n := n * 10 + (s[i] as int - '0' as int);
        }
        i := i + 1;
    }

    if negative {
        n := -n;
    }
}

method solve(input: string) returns (result: string)
    ensures (forall a, b, c, d: int :: 
        ValidParse(input, a, b, c, d) ==> 
        (result == "Left\n" <==> a + b > c + d) &&
        (result == "Right\n" <==> a + b < c + d) &&
        (result == "Balanced\n" <==> a + b == c + d))
    ensures ValidParseable(input) && AllPartsAreIntegers(input) ==> (result == "Left\n" || result == "Right\n" || result == "Balanced\n")
    ensures (!ValidParseable(input) || !AllPartsAreIntegers(input)) ==> result == ""
{
    var parts := SplitString(input);
    if |parts| < 4 {
        return "";
    }

    if !AllPartsValidIntegers(parts) {
        return "";
    }

    var a := StringToInt(parts[0]);
    var b := StringToInt(parts[1]);
    var c := StringToInt(parts[2]);
    var d := StringToInt(parts[3]);

    var leftTotal := a + b;
    var rightTotal := c + d;

    if leftTotal > rightTotal {
        result := "Left\n";
    } else if leftTotal < rightTotal {
        result := "Right\n";
    } else {
        result := "Balanced\n";
    }
}
