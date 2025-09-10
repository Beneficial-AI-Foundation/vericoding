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
function SplitLines(s: string): seq<string>
    ensures |SplitLines(s)| >= 1
{
    if |s| == 0 then [""]
    else
        var lines: seq<string> := [];
        var start := 0;
        var i := 0;
        while i < |s|
            invariant 0 <= start <= i <= |s|
            invariant |lines| >= 0
        {
            if s[i] == '\n' {
                lines := lines + [s[start..i]];
                start := i + 1;
            }
            i := i + 1;
        }
        lines := lines + [s[start..|s|]];
        lines
}

function SplitSpaces(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var parts: seq<string> := [];
        var start := 0;
        var i := 0;
        while i < |s|
            invariant 0 <= start <= i <= |s|
            invariant |parts| >= 0
        {
            if s[i] == ' ' {
                if start < i {
                    parts := parts + [s[start..i]];
                }
                start := i + 1;
            }
            i := i + 1;
        }
        if start < |s| {
            parts := parts + [s[start..|s|]];
        } else if |parts| == 0 && |s| > 0 {
            parts := [""];
        }
        parts
}

function StringToInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' || (i == 0 && s[i] == '-')
    requires s != "-"
{
    if s[0] == '-' then
        -StringToNat(s[1..])
    else
        StringToNat(s)
}

function StringToNat(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 1 then
        s[0] as int - '0' as int
    else
        (s[0] as int - '0' as int) * pow10(|s| - 1) + StringToNat(s[1..])
}

function pow10(n: nat): int
{
    if n == 0 then 1
    else 10 * pow10(n - 1)
}

lemma StringToIntNonNegative(s: string)
    requires IsValidInteger(s) && s[0] != '-'
    ensures StringToInt(s) >= 0
{
}

lemma StringToIntNegative(s: string)
    requires IsValidInteger(s) && s[0] == '-'
    ensures StringToInt(s) <= -1
{
}

lemma ValidGrasshopperLineImpliesValidCoords(line: string, n: int)
    requires ValidGrasshopperLine(line, n)
    ensures var parts := SplitSpaces(line);
            var x := StringToInt(parts[0]);
            var y := StringToInt(parts[1]);
            0 <= x <= n && 0 <= y <= n
{
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
    var n := GetN(input);
    var d := GetD(input);
    var m := GetNumberOfGrasshoppers(input);
    result := [];
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == (if IsInsideCornfield(GetGrasshopper(input, j), n, d) then "YES" else "NO")
    {
        var grasshopper := GetGrasshopper(input, i);
        if IsInsideCornfield(grasshopper, n, d) {
            result := result + ["YES"];
        } else {
            result := result + ["NO"];
        }
        i := i + 1;
    }
}
// </vc-code>

