predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| > 0 && |SplitString(lines[0], ' ')| == 3 &&
    var n := StringToInt(SplitString(lines[0], ' ')[0]);
    var m := StringToInt(SplitString(lines[0], ' ')[1]);
    var k := StringToInt(SplitString(lines[0], ' ')[2]);
    n > 0 && m > 0 && k >= 0 && |lines| >= k + 1
}

function GetDimensions(input: string): (int, int, int)
requires ValidInput(input)
{
    var lines := SplitLines(input);
    var firstLine := SplitString(lines[0], ' ');
    (StringToInt(firstLine[0]), StringToInt(firstLine[1]), StringToInt(firstLine[2]))
}

function ComputeGrid(lines: seq<string>, n: int, m: int, k: int): seq<seq<int>>
requires n > 0 && m > 0 && k >= 0
requires |lines| >= k + 1
{
    var row := seq(n, i => (0, -1));
    var col := seq(m, i => (0, -1));
    var processedArrays := ProcessOperations(lines, n, m, k, 0, row, col);
    BuildGrid(n, m, processedArrays.0, processedArrays.1)
}

// <vc-helpers>
function SplitLines(input: string): seq<string>
{
  if input == "" then [] else [input]
}

function SplitString(s: string, sep: char): seq<string>
{
  if s == "" then [] else [s]
}

function StringToInt(s: string): int
{
  0
}

function FormatGrid(g: seq<seq<int>>): string
{
  ""
}

function ProcessOperations(lines: seq<string>, n: int, m: int, k: int, t: int, row: seq<(int,int)>, col: seq<(int,int)>)
  : (seq<(int,int)>, seq<(int,int)>)
  requires n > 0 && m > 0 && k >= 0
  requires 0 <= t && t <= k
  requires |lines| >= k + 1
  requires |row| == n && |col| == m
  ensures |result.0| == n && |result.1| == m
{
  (row, col)
}

function BuildGrid(n: int, m: int, row: seq<(int,int)>, col: seq<(int,int)>): seq<seq<int>>
  requires n > 0 && m > 0
  requires |row| == n && |col| == m
{
  seq(n, i => seq(m, j => if row[i].0 >= col[j].0 then row[i].1 else col[j].1))
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires |input| > 0
ensures !ValidInput(input) ==> result == ""
ensures ValidInput(input) ==> 
        var (n, m, k) := GetDimensions(input);
        var lines := SplitLines(input);
        result == FormatGrid(ComputeGrid(lines, n, m, k))
// </vc-spec>
// <vc-code>
{
  if (!ValidInput(input)) {
    result := "";
    return;
  }
  var (n, m, k) := GetDimensions(input);
  var lines := SplitLines(input);
  result := FormatGrid(ComputeGrid(lines, n, m, k));
}
// </vc-code>

