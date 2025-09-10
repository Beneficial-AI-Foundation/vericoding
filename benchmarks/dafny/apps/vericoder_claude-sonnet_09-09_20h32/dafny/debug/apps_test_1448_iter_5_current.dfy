function ValidInput(input: string): bool
{
    var lines := SplitLines(input);
    |lines| >= 3 && 
    ValidFirstLine(lines[0]) &&
    ValidSecondLine(lines[1]) &&
    ValidGrasshopperLinesSimple(lines) &&
    var firstLine := SplitSpaces(lines[0]);
    var n := StringToInt(firstLine[0]);
    var d := StringToInt(firstLine[1]);
    var m := StringToInt(lines[1]);
    d >= 1 && d < n && n <= 100 &&
    m >= 1 && m <= 100 &&
    |lines| >= 2 + m &&
    forall i {:trigger ValidGrasshopperLine(lines[2 + i], n)} :: 0 <= i < m ==> ValidGrasshopperLine(lines[2 + i], n)
}

function ValidFirstLine(line: string): bool
{
    var parts := SplitSpaces(line);
    |parts| == 2 && IsValidInteger(parts[0]) && IsValidInteger(parts[1])
}

function ValidSecondLine(line: string): bool
{
    IsValidInteger(line)
}

function ValidGrasshopperLinesSimple(lines: seq<string>): bool
{
    |lines| >= 3 &&
    var m := StringToInt(lines[1]);
    |lines| >= 2 + m
}

function ValidGrasshopperLine(line: string, n: int): bool
{
    var parts := SplitSpaces(line);
    |parts| == 2 && IsValidInteger(parts[0]) && IsValidInteger(parts[1]) &&
    StringToInt(parts[0]) >= 0 && StringToInt(parts[0]) <= n &&
    StringToInt(parts[1]) >= 0 && StringToInt(parts[1]) <= n
}

function IsValidInteger(s: string): bool
{
    |s| > 0 && (s[0] != '-' ==> forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9') &&
    (s[0] == '-' ==> |s| > 1 && forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9')
}

function GetN(input: string): int
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var firstLine := SplitSpaces(lines[0]);
    StringToInt(firstLine[0])
}

function GetD(input: string): int
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var firstLine := SplitSpaces(lines[0]);
    StringToInt(firstLine[1])
}

function GetNumberOfGrasshoppers(input: string): int
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    StringToInt(lines[1])
}

function GetGrasshopper(input: string, i: int): (int, int)
    requires ValidInput(input)
    requires 0 <= i < GetNumberOfGrasshoppers(input)
{
    var lines := SplitLines(input);
    var coords := SplitSpaces(lines[2 + i]);
    assert ValidGrasshopperLine(lines[2 + i], GetN(input));
    assert |coords| == 2;
    (StringToInt(coords[0]), StringToInt(coords[1]))
}

function IsInsideCornfield(grasshopper: (int, int), n: int, d: int): bool
{
    var (x, y) := grasshopper;
    x + y >= d && x + y <= 2 * n - d && x - y >= -d && x - y <= d
}

// <vc-helpers>
function SplitLines(input: string): seq<string>
{
    if |input| == 0 then []
    else 
        var lines := SplitLinesHelper(input, 0, []);
        lines
}

function SplitLinesHelper(input: string, start: int, acc: seq<string>): seq<string>
    requires 0 <= start <= |input|
    decreases |input| - start
{
    if start >= |input| then acc
    else
        var end := FindNewline(input, start);
        if end == -1 then
            acc + [input[start..]]
        else if end < start then
            acc
        else if end >= start then
            SplitLinesHelper(input, end + 1, acc + [input[start..end]])
        else
            acc
}

function FindNewline(input: string, start: int): int
    requires 0 <= start <= |input|
    decreases |input| - start
{
    if start >= |input| then -1
    else if input[start] == '\n' then start
    else FindNewline(input, start + 1)
}

function SplitSpaces(line: string): seq<string>
{
    if |line| == 0 then []
    else SplitSpacesHelper(line, 0, [])
}

function SplitSpacesHelper(line: string, start: int, acc: seq<string>): seq<string>
    requires 0 <= start <= |line|
    decreases |line| - start
{
    if start >= |line| then acc
    else
        var end := FindSpace(line, start);
        if end == -1 then
            acc + [line[start..]]
        else if end < start then
            acc
        else if end >= start then
            SplitSpacesHelper(line, end + 1, acc + [line[start..end]])
        else
            acc
}

function FindSpace(line: string, start: int): int
    requires 0 <= start <= |line|
    decreases |line| - start
{
    if start >= |line| then -1
    else if line[start] == ' ' then start
    else FindSpace(line, start + 1)
}

function StringToInt(s: string): int
    requires IsValidInteger(s)
{
    if |s| == 0 then 0
    else if s[0] == '-' then -StringToIntHelper(s[1..])
    else StringToIntHelper(s)
}

function StringToIntHelper(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 1 then s[0] as int - '0' as int
    else StringToIntHelper(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

lemma ValidInputPreservesGrasshopperLine(input: string, i: int)
    requires ValidInput(input)
    requires 0 <= i < GetNumberOfGrasshoppers(input)
    ensures ValidGrasshopperLine(SplitLines(input)[2 + i], GetN(input))
{
    var lines := SplitLines(input);
    var m := StringToInt(lines[1]);
    assert m == GetNumberOfGrasshoppers(input);
    assert i < m;
    assert ValidGrasshopperLine(lines[2 + i], GetN(input));
}

lemma GetGrasshopperProperties(input: string, i: int)
    requires ValidInput(input)
    requires 0 <= i < GetNumberOfGrasshoppers(input)
    ensures var (x, y) := GetGrasshopper(input, i); 
            0 <= x <= GetN(input) && 0 <= y <= GetN(input)
{
    var lines := SplitLines(input);
    var coords := SplitSpaces(lines[2 + i]);
    ValidInputPreservesGrasshopperLine(input, i);
    assert ValidGrasshopperLine(lines[2 + i], GetN(input));
    assert |coords| == 2;
    assert StringToInt(coords[0]) >= 0 && StringToInt(coords[0]) <= GetN(input);
    assert StringToInt(coords[1]) >= 0 && StringToInt(coords[1]) <= GetN(input);
}

lemma ValidInputEnsuresValidSecondLine(input: string)
    requires ValidInput(input)
    ensures var lines := SplitLines(input);
            |lines| >= 2 && IsValidInteger(lines[1])
{
    var lines := SplitLines(input);
    assert |lines| >= 3;
    assert ValidSecondLine(lines[1]);
    assert IsValidInteger(lines[1]);
}

lemma ValidInputEnsuresIsValidIntegerForLines(input: string)
    requires ValidInput(input)
    ensures var lines := SplitLines(input);
            |lines| >= 2 && IsValidInteger(lines[1]) &&
            var firstLine := SplitSpaces(lines[0]);
            |firstLine| >= 2 && IsValidInteger(firstLine[0]) && IsValidInteger(firstLine[1])
{
    var lines := SplitLines(input);
    assert ValidFirstLine(lines[0]);
    assert ValidSecondLine(lines[1]);
    var firstLine := SplitSpaces(lines[0]);
    assert |firstLine| == 2;
    assert IsValidInteger(firstLine[0]);
    assert IsValidInteger(firstLine[1]);
    assert IsValidInteger(lines[1]);
}

lemma ProveIsValidIntegerPreconditions(input: string)
    requires ValidInput(input)
    ensures var lines := SplitLines(input);
            |lines| >= 2 &&
            var firstLine := SplitSpaces(lines[0]);
            |firstLine| >= 2 &&
            IsValidInteger(firstLine[0]) &&
            IsValidInteger(firstLine[1]) &&
            IsValidInteger(lines[1])
{
    ValidInputEnsuresIsValidIntegerForLines(input);
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: seq<string>)
    requires |input| > 0
    requires ValidInput(input)
    ensures |result| == GetNumberOfGrasshoppers(input)
    ensures forall i :: 0 <= i < |result| ==> result[i] == "YES" || result[i] == "NO"
    ensures forall i :: 0 <= i < |result| ==> 
        result[i] == (if IsInsideCornfield(GetGrasshopper(input, i), GetN(input), GetD(input)) then "YES" else "NO")
// </vc-spec>
// <vc-code>
{
    ProveIsValidIntegerPreconditions(input);
    
    var lines := SplitLines(input);
    var firstLine := SplitSpaces(lines[0]);
    
    var n := StringToInt(firstLine[0]);
    var d := StringToInt(firstLine[1]);
    var m := StringToInt(lines[1]);
    
    result := [];
    var i := 0;
    
    while i < m
        invariant 0 <= i <= m
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == "YES" || result[j] == "NO"
        invariant forall j :: 0 <= j < i ==> 
            result[j] == (if IsInsideCornfield(GetGrasshopper(input, j), n, d) then "YES" else "NO")
    {
        GetGrasshopperProperties(input, i);
        var grasshopper := GetGrasshopper(input, i);
        var inside := IsInsideCornfield(grasshopper, n, d);
        
        if inside {
            result := result + ["YES"];
        } else {
            result := result + ["NO"];
        }
        
        i := i + 1;
    }
}
// </vc-code>

