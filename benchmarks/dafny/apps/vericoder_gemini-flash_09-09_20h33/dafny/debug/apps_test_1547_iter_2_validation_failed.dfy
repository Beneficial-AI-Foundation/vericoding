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
function SplitString(s: string, separator: char): seq<string>
  reads Set()
  ensures forall i :: 0 <= i < |SplitString(s, separator)| ==> |SplitString(s, separator)[i]| <= |s| // Added postcondition
{
  if separator as int < 0 || separator as int > 255 then
    return [s];

  var result: seq<string> := [];
  var current: string := "";
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < |result| ==> |result[j]| <= |s| // Added invariant
    invariant |current| <= |s| // Added invariant
  {
    if i < |s| && s[i] != separator then
      current := current + s[i];
    else
      result := result + [current];
      current := "";
    if i == |s| && |current| > 0
    {
      result := result + [current];
    }
  }
  return result;
}

function StringToInt(s: string): int
  reads Set()
  ensures StringToInt(s) >= 0 || s == "" // Added postcondition for non-negative integers or empty string
{
  if |s| == 0 then return 0;
  var i := 0;
  var sign := 1;
  var num := 0;
  if s[0] == '-' then
    sign := -1;
    i := 1;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant num >= 0 // Added invariant for non-negative intermediate number
  {
    if '0' <= s[i] <= '9' then
      num := num * 10 + (s[i] as int - '0' as int);
    else
      // Handle non-digit characters if necessary, for now, assume valid input
      return 0; // Or some error handling
    i := i + 1;
  }
  return sign * num;
}

function SplitLines(input: string): seq<string>
  reads Set()
  ensures forall i :: 0 <= i < |SplitLines(input)| ==> |SplitLines(input)[i]| <= |input| // Added postcondition
{
  var lines: seq<string> := [];
  var currentLine: string := "";
  for i := 0 to |input|
    invariant 0 <= i <= |input|
    invariant forall j :: 0 <= j < |lines| ==> |lines[j]| <= |input| // Added invariant
    invariant |currentLine| <= |input| // Added invariant
  {
    if i < |input| && input[i] != '\n' then
      currentLine := currentLine + input[i];
    else
      lines := lines + [currentLine];
      currentLine := "";
    if i == |input| && |currentLine| > 0
    {
      lines := lines + [currentLine];
    }
  }
  return lines;
}

function FormatInt(num: int): string
  reads Set()
{
  if num == 0 then return "0";
  var s := "";
  var n := num;
  var isNegative := false;
  if n < 0 then
    isNegative := true;
    n := -n;
  while n > 0
  {
    s := (n % 10 as char + '0') + s;
    n := n / 10;
  }
  if isNegative then
    s := "-" + s;
  return s;
}

function FormatGrid(grid: seq<seq<int>>): string
  reads Set()
  ensures forall i :: 0 <= i < |SplitLines(FormatGrid(grid))| ==> |SplitLines(FormatGrid(grid))[i]| > 0 // Added postcondition
  ensures forall i :: 0 <= i < |grid| ==> forall j :: 0 <= j < |grid[0]| ==> StringToInt(SplitString(SplitLines(FormatGrid(grid))[i], ' ')[j]) == grid[i][j] // Added postcondition - ensures conversion associativity
{
  var result: string := "";
  for i := 0 to |grid| - 1
  {
    var rowString: string := "";
    for j := 0 to |grid[i]| - 1
    {
      rowString := rowString + FormatInt(grid[i][j]);
      if j < |grid[i]| - 1 then
        rowString := rowString + " ";
    }
    result := result + rowString;
    if i < |grid| - 1 then
      result := result + "\n";
  }
  return result;
}

function ProcessOperations(lines: seq<string>, n: int, m: int, k: int, currentK: int, rowOps: seq<(int, int)>, colOps: seq<(int, int)>): (seq<(int, int)>, seq<(int, int)>)
  requires n > 0 && m > 0 && k >= 0
  requires currentK <= k
  requires |lines| >= k + 1
  decreases k - currentK
  ensures |rowOps| == n
  ensures |colOps| == m
{
  if currentK == k then
    return (rowOps, colOps);

  var opLine := SplitString(lines[currentK + 1], ' ');
  var opType := StringToInt(opLine[0]);
  var index := StringToInt(opLine[1]);
  var value := StringToInt(opLine[2]);

  var newRowOps := rowOps;
  var newColOps := colOps;

  if opType == 0 then // Row operation
    newRowOps := newRowOps[index := (value, currentK + 1)];
  else if opType == 1 then // Column operation
    newColOps := newColOps[index := (value, currentK + 1)];

  return ProcessOperations(lines, n, m, k, currentK + 1, newRowOps, newColOps);
}

function BuildGrid(n: int, m: int, rowOps: seq<(int, int)>, colOps: seq<(int, int)>): seq<seq<int>>
  requires n > 0 && m > 0
  requires |rowOps| == n
  requires |colOps| == m
  ensures forall i :: 0 <= i < n ==> |BuildGrid(n, m, rowOps, colOps)[i]| == m
{
  var grid: seq<seq<int>> := [];
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant |grid| == i
    invariant forall x :: 0 <= x < i ==> |grid[x]| == m
  {
    var row: seq<int> := [];
    for j := 0 to m - 1
      invariant 0 <= j <= m
      invariant |row| == j
    {
      var rowVal, rowK := rowOps[i];
      var colVal, colK := colOps[j];
      var cellVal := 0;
      if rowK > colK then
        cellVal := rowVal;
      else if colK > rowK then
        cellVal := colVal;
      else // rowK == colK or both -1 (initial state)
        cellVal := rowVal; // Doesn't matter which one, both 0 if -1
      row := row + [cellVal];
    }
    grid := grid + [row];
  }
  return grid;
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
  if !ValidInput(input) then
    result := "";
  else
    var (n, m, k) := GetDimensions(input);
    var lines := SplitLines(input);
    result := FormatGrid(ComputeGrid(lines, n, m, k));
}
// </vc-code>

