Given integers n and d, determine for each grasshopper whether their position 
is inside or on the boundary of a cornfield quadrilateral with vertices at 
(0,d), (d,0), (n,n-d), (n-d,n). Output "YES" if inside/on boundary, "NO" otherwise.

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

function SplitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var i := FindChar(s, '\n');
        if i == -1 then [s]
        else if i >= 0 && i < |s| then [s[..i]] + SplitLines(s[i+1..])
        else [s]
}

function SplitSpaces(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var i := FindChar(s, ' ');
        if i == -1 then [s]
        else if i >= 0 && i < |s| then [s[..i]] + SplitSpaces(s[i+1..])
        else [s]
}

function FindChar(s: string, c: char): int
{
    FindCharHelper(s, c, 0)
}

function FindCharHelper(s: string, c: char, index: int): int
    requires 0 <= index
    decreases |s| - index
{
    if index >= |s| then -1
    else if s[index] == c then index
    else FindCharHelper(s, c, index + 1)
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then -StringToIntHelper(s[1..], 0)
    else StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, acc: int): int
{
    if |s| == 0 then acc
    else
        var digit := s[0] as int - '0' as int;
        StringToIntHelper(s[1..], acc * 10 + digit)
}

method solve(input: string) returns (result: seq<string>)
    requires |input| > 0
    requires ValidInput(input)
    ensures |result| == GetNumberOfGrasshoppers(input)
    ensures forall i :: 0 <= i < |result| ==> result[i] == "YES" || result[i] == "NO"
    ensures forall i :: 0 <= i < |result| ==> 
        result[i] == (if IsInsideCornfield(GetGrasshopper(input, i), GetN(input), GetD(input)) then "YES" else "NO")
{
    var lines := SplitLines(input);
    var firstLine := SplitSpaces(lines[0]);
    var n := StringToInt(firstLine[0]);
    var d := StringToInt(firstLine[1]);
    var m := StringToInt(lines[1]);

    result := [];

    for i := 0 to m
        invariant 0 <= i <= m
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == "YES" || result[j] == "NO"
        invariant forall j :: 0 <= j < i ==> 
            result[j] == (if IsInsideCornfield(GetGrasshopper(input, j), n, d) then "YES" else "NO")
    {
        var tmpCall1 := SplitSpaces(lines[2 + i]);
        var coords := tmpCall1;
        assert ValidGrasshopperLine(lines[2 + i], n);
        assert |coords| == 2;
        var x := StringToInt(coords[0]);
        var y := StringToInt(coords[1]);

        if (x + y >= d && x + y <= 2 * n - d && x - y >= -d && x - y <= d) {
            result := result + ["YES"];
        } else {
            result := result + ["NO"];
        }
    }
}
