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
ghost function SplitLines(s: string): seq<string> {
  SplitLinesAux(s, 0, 0)
}

ghost function SplitLinesAux(s: string, start: int, i: int): seq<string>
  requires 0 <= start <= i <= |s|
  decreases |s| - i
{
  if i == |s| then
    if start == |s| then [] else [s[start..]]
  else if s[i] == '\n' then
    if start == i then 
      SplitLinesAux(s, i+1, i+1)
    else 
      [s[start..i]] + SplitLinesAux(s, i+1, i+1)
  else 
    SplitLinesAux(s, start, i+1)
}

ghost function SplitSpaces(s: string): seq<string> {
  SplitSpacesAux(s, 0, 0)
}

ghost function SplitSpacesAux(s: string, start: int, i: int): seq<string>
  requires 0 <= start <= i <= |s|
  decreases |s| - i
{
  if i == |s| then
    if start == |s| then [] else [s[start..]]
  else if s[i] == ' ' then
    if start == i then 
      SplitSpacesAux(s, i+1, i+1)
    else 
      [s[start..i]] + SplitSpacesAux(s, i+1, i+1)
  else 
    SplitSpacesAux(s, start, i+1)
}

ghost function DigitsToInt(s: string): int
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  decreases |s|
{
  if |s| == 0 then 0
  else 
    var prev := DigitsToInt(s[0..|s|-1]);
    prev * 10 + (s[|s|-1] as int - '0' as int)
}

ghost function StringToInt(s: string): int
  requires IsValidInteger(s)
{
  if s[0] == '-' then 
    -DigitsToInt(s[1:])
  else 
    DigitsToInt(s)
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
    var arr := new string[m];
    for i := 0 to m
        invariant 0 <= i <= m
        invariant forall j :: 0 <= j < i ==> 
            arr[j] == (if IsInsideCornfield(GetGrasshopper(input, j), n, d) then "YES" else "NO")
    {
        var g := GetGrasshopper(input, i);
        arr[i] := if IsInsideCornfield(g, n, d) then "YES" else "NO";
    }
    return arr[..];
}
// </vc-code>

