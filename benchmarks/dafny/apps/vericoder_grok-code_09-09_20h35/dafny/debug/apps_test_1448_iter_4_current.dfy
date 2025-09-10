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
function StringToInt(s: string): int
  requires IsValidInteger(s)
{
  if |s| > 0 && s[0] == '-' then
    -StringToIntSimple(s[1..])
  else
    StringToIntSimple(s)
}

function StringToIntSimple(s: string): int
  requires |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
  StringToIntHelper(s, 0, 0)
}

function StringToIntHelper(s: string, i: nat, acc: int): int
  decreases |s| - i
  requires i <= |s|
  requires forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
{
  if i == |s| then acc
  else StringToIntHelper(s, i + 1, acc * 10 + (s[i] - '0'))
}

function SplitSpaces(s: string): seq<string>
{
  SplitSpacesHelper(s, 0)
}

function SplitSpacesHelper(s: string, i: nat): seq<string>
  requires i <= |s|
  decreases |s| - i
{
  if i == |s| then []
  else
    var start := SkipSpaces(s, i);
    if start == |s| then []
    else
      var end := FindEndOfWord(s, start);
      [s[start..end]] + SplitSpacesHelper(s, end)
}

function SkipSpaces(s: string, i: nat): nat
  requires i <= |s|
  decreases |s| - i
{
  if i == |s| || s[i] != ' ' then i
  else SkipSpaces(s, i + 1)
}

function FindEndOfWord(s: string, i: nat): nat
  requires i <= |s|
  decreases |s| - i
{
  if i == |s| || s[i] == ' ' then i
  else FindEndOfWord(s, i + 1)
}

function SplitLines(s: string): seq<string>
{
  SplitLinesHelper(s, 0)
}

function SplitLinesHelper(s: string, i: nat): seq<string>
  requires i <= |s|
  decreases |s| - i
{
  if i == |s| then []
  else
    var end := FindEndOfLine(s, i);
    [s[i..end]] + if end == |s| then [] else SplitLinesHelper(s, end + 1)
}

function FindEndOfLine(s: string, i: nat): nat
  requires i <= |s|
  decreases |s| - i
{
  if i == |s| || s[i] == '\n' then i
  else FindEndOfLine(s, i + 1)
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
var n := GetN(input);
  var d := GetD(input);
  var m := GetNumberOfGrasshoppers(input);
  var result: seq<string> := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == (if IsInsideCornfield(GetGrasshopper(input, j), n, d) then "YES" else "NO")
    decreases m - i
  {
    var grass := GetGrasshopper(input, i);
    var inside := IsInsideCornfield(grass, n, d);
    var str := if inside then "YES" else "NO";
    result := result + [str];
    i := i + 1;
  }
  result
// </vc-code>

