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
  ensures forall i, j :: 0 <= i < j < |SplitLines(input)| ==> SplitLines(input)[i] != "\n"
  ensures forall i :: 0 <= i < |SplitLines(input)| ==> !SplitLines(input)[i].Contains('\n')
{
  if input.Contains('\n')
  then
    var newlineIndex := input.IndexOf('\n');
    [input[..newlineIndex]] + SplitLines(input[newlineIndex + 1 ..])
  else
    [input]
}

function SplitSpaces(s: string): seq<string>
  ensures forall i, j :: 0 <= i < j < |SplitSpaces(s)| ==> SplitSpaces(s)[i] != " "
  ensures forall i :: 0 <= i < |SplitSpaces(s)| ==> !SplitSpaces(s)[i].Contains(' ')
{
  if s.Contains(' ')
  then
    var spaceIndex := s.IndexOf(' ');
    [s[..spaceIndex]] + SplitSpaces(s[spaceIndex + 1 ..])
  else
    [s]
}

function StringToInt(s: string): int
  requires IsValidInteger(s)
{
  if s[0] == '-' then
    -StringToIntPositive(s[1..])
  else
    StringToIntPositive(s)
}

function StringToIntPositive(s: string): int
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  requires |s| > 0
{
  if |s| == 1 then
    s[0] as int - '0' as int
  else
    (s[0] as int - '0' as int) * (10 * (|s|-1)) + StringToIntPositive(s[1..])
}

// Lemma to help with StringToInt on concatenated strings
lemma StringToIntConcatLemma(s1: string, s2: string)
  requires forall i :: 0 <= i < |s1| ==> '0' <= s1[i] <= '9'
  requires forall i :: 0 <= i < |s2| ==> '0' <= s2[i] <= '9'
  requires |s1| > 0
  requires |s2| > 0
  ensures StringToIntPositive(s1 + s2) == StringToIntPositive(s1) * (10 power |s2|) + StringToIntPositive(s2)
{
  if |s1| == 1 {
    calc {
      StringToIntPositive(s1 + s2);
      (s1[0] as int - '0' as int) * (10 power |s2|) + StringToIntPositive(s2);
      StringToIntPositive(s1) * (10 power |s2|) + StringToIntPositive(s2);
    }
  } else {
    var s1_first := s1[0];
    var s1_rest := s1[1..];
    var s_concat_rest := s1_rest + s2;

    calc {
      StringToIntPositive(s1 + s2);
      { StringToIntConcatLemma(s1_rest, s2); }
      (s1_first as int - '0' as int) * (10 power (|s1| -1 + |s2|)) + StringToIntPositive(s_concat_rest);
      (s1_first as int - '0' as int) * (10 power (|s1| -1 + |s2|)) + (StringToIntPositive(s1_rest) * (10 power |s2|) + StringToIntPositive(s2));
      (s1_first as int - '0' as int) * (10 power ((|s1|-1) + |s2|)) + StringToIntPositive(s1_rest) * (10 power |s2|) + StringToIntPositive(s2);
      ( (s1_first as int - '0' as int) * (10 power (|s1| - 1)) + StringToIntPositive(s1_rest) ) * (10 power |s2|) + StringToIntPositive(s2);
      StringToIntPositive(s1) * (10 power |s2|) + StringToIntPositive(s2);
    }
  }
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
    var result: seq<string> := [];

    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==>
            result[k] == (if IsInsideCornfield(GetGrasshopper(input, k), n, d) then "YES" else "NO")
    {
        var grasshopper := GetGrasshopper(input, i);
        if IsInsideCornfield(grasshopper, n, d) {
            result := result + ["YES"];
        } else {
            result := result + ["NO"];
        }
        i := i + 1;
    }
    return result;
}
// </vc-code>

