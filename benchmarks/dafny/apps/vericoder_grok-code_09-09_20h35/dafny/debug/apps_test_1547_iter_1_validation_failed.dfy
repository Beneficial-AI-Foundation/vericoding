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
// Auxiliary functions assumed or defined for string manipulation
// Assuming these are predefined or part of Dafny's standard library
ghost function SplitString(s: string, c: char): seq<string>
ghost function SplitLines(s: string): seq<string>
ghost function StringToInt(s: string): int requires |s| > 0
ghost function StringFromInt(i: int): string

// Join function for sequences of strings
function Join(seqs: seq<string>, sep: string): string
{
  if |seqs| == 0 then "" else
    var first := seqs[0];
    (if |seqs| == 1 then first else first + sep + Join(seqs[1..], sep))
}

// Function to process operations and update row and column states
function ProcessOperations(lines: seq<string>, n: int, m: int, k: int, idx: int, row: seq<(int, int)>, col: seq<(int, int)>): (seq<(int, int)>, seq<(int, int)>)
requires n > 0 && m > 0 && k >= 0
requires |lines| >= k + 1
requires 0 <= idx <= k
requires |row| == n && |col| == m
decreases k - idx
{
  if idx == k then (row, col)
  else
    var op := SplitString(lines[idx + 1], ' ');
    assume 3 == |op|; // Assume valid operation format
    var type := StringToInt(op[0]);
    var idx2 := StringToInt(op[1]);
    var v := StringToInt(op[2]);
    if type == 1 {
      assume 1 <= idx2 <= n; // Assume valid row index
      ProcessOperations(lines, n, m, k, idx + 1, row[idx2 - 1 := (v, idx)], col)
    } else {
      assume 1 <= idx2 <= m; // Assume valid column index
      ProcessOperations(lines, n, m, k, idx + 1, row, col[idx2 - 1 := (v, idx)])
    }
}

// Function to build the grid based on row and column states
function BuildGrid(n: int, m: int, row: seq<(int, int)>, col: seq<(int, int)>): seq<seq<int>>
requires |row| == n && |col| == m
{
  seq(n, i => seq(m, j => {
    var rSet, rVal := row[i].1 != -1, row[i].0;
    var cSet, cVal := col[j].1 != -1, col[j].0;
    if rSet && ( !cSet || row[i].1 > col[j].1 ) then rVal
    else if cSet then cVal
    else 0
  }))
}

// Function to format the grid into a string
function FormatGrid(grid: seq<seq<int>>): string
{
  Join(seq(|grid|, i => Join(seq(|grid[i]|, j => StringFromInt(grid[i][j])), " ")), "\n")
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
  } else {
    var (n, m, k) := GetDimensions(input);
    var lines := SplitLines(input);
    var grid := ComputeGrid(lines, n, m, k);
    result := FormatGrid(grid);
  }
}
// </vc-code>

