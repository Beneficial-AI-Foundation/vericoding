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
  reads Ghost
{
  if input == "" then
    []
  else
    var lines := new seq<string>(0, _ => "");
    var startIndex := 0;
    var i := 0;
    while i < |input|
      invariant 0 <= i <= |input|
      invariant 0 <= startIndex <= i
      invariant forall j :: 0 <= j < |lines| ==> lines[j].IsWellFormedString()
    {
      if input[i] == '\n' {
        lines := lines + [input[startIndex>..i]];
        startIndex := i + 1;
      }
      i := i + 1;
    }
    lines := lines + [input[startIndex>..|input|]];
    lines
}

function SplitString(input: string, delimiter: char): seq<string>
  reads Ghost
{
  if input == "" then
      []
  else
    var result := new seq<string>(0, _ => "");
    var startIndex := 0;
    var i := 0;
    while i < |input|
      invariant 0 <= i <= |input|
      invariant 0 <= startIndex <= i
      invariant forall j :: 0 <= j < |result| ==> result[j].IsWellFormedString()
    {
      if input[i] == delimiter {
        result := result + [input[startIndex>..i]];
        startIndex := i + 1;
      }
      i := i + 1;
    }
    result := result + [input[startIndex>..|input|]];
    result
}

function StringToInt(s: string): int
  reads Ghost
{
  var i := 0;
  var sign := 1;
  var num := 0;
  if |s| > 0 && s[0] == '-' {
    sign := -1;
    i := 1;
  }
  while i < |s|
    invariant 0 <= i <= |s|
    invariant num >= 0
    invariant forall k :: (if sign == 1 then 0 else 1) <= k < i ==> '0' <= s[k] <= '9'
  {
    if '0' <= s[i] <= '9' {
      num := num * 10 + (s[i] as int - '0' as int);
    } else {
      assert false; // Should not happen for valid integer strings
    }
    i := i + 1;
  }
  sign * num
}

function ProcessOperations(lines: seq<string>, n: int, m: int, k: int, currentOperation: int, row: seq<(int, int)>, col: seq<(int, int)>): (seq<(int, int)>, seq<(int, int)>)
  requires n > 0 && m > 0 && k >= 0
  requires currentOperation <= k
  requires |lines| >= k + 1
  requires |row| == n
  requires |col| == m
  reads Ghost
{
  if currentOperation == k then
    (row, col)
  else
    var opLine := SplitString(lines[currentOperation + 1], ' ');
    var opType := StringToInt(opLine[0]);
    var index := StringToInt(opLine[1]) - 1;
    var value := StringToInt(opLine[2]);

    var newRow := row;
    var newCol := col;

    if opType == 0 { // Row operation
      newRow := newRow[index := (value, currentOperation)];
    } else { // Column operation
      newCol := newCol[index := (value, currentOperation)];
    }
    ProcessOperations(lines, n, m, k, currentOperation + 1, newRow, newCol)
}

function BuildGrid(n: int, m: int, row: seq<(int,int)>, col: seq<(int,int)>): seq<seq<int>>
  requires n > 0 && m > 0
  requires |row| == n
  requires |col| == m
  reads Ghost
{
  var grid := new seq<seq<int>>(n, i => new seq<int>(m, j => 0)); // Initialize with zeros
  for i := 0 to n-1
    invariant 0 <= i <= n
    invariant |grid| == n
    invariant forall r :: 0 <= r < i ==> |grid[r]| == m
    invariant forall r, c :: 0 <= r < i && 0 <= c < m ==>
      var rowVal, rowTime := row[r];
      var colVal, colTime := col[c];
      (rowTime > colTime && rowTime != -1) ==> grid[r][c] == rowVal
    invariant forall r, c :: 0 <= r < i && 0 <= c < m ==>
       (colTime > rowTime && colTime != -1) ==> grid[r][c] == colVal
    invariant forall r, c :: 0 <= r < i && 0 <= c < m ==>
        (colTime == rowTime && colTime == -1) ==> grid[r][c] == 0
  {
    for j := 0 to m-1
      invariant 0 <= j <= m
      invariant |grid| == n
      invariant |grid[i]| == m
      invariant forall c :: 0 <= c < j ==>
        var rowVal, rowTime := row[i];
        var colVal, colTime := col[c];
        (rowTime > colTime && rowTime != -1) ==> grid[i][c] == rowVal
      invariant forall c :: 0 <= c < j ==>
        (colTime > rowTime && colTime != -1) ==> grid[i][c] == colVal
      invariant forall c :: 0 <= c < j ==>
        (colTime == rowTime && colTime == -1) ==> grid[i][c] == 0
      invariant forall r :: 0 <= r < i ==> |grid[r]| == m
      invariant forall r, c_other :: 0 <= r < i && 0 <= c_other < m ==>
        var rowVal_other, rowTime_other := row[r];
        var colVal_other, colTime_other := col[c_other];
        (rowTime_other > colTime_other && rowTime_other != -1) ==> grid[r][c_other] == rowVal_other
      invariant forall r, c_other :: 0 <= r < i && 0 <= c_other < m ==>
        (colTime_other > rowTime_other && colTime_other != -1) ==> grid[r][c_other] == colVal_other
      invariant forall r, c_other :: 0 <= r < i && 0 <= c_other < m ==>
        (colTime_other == rowTime_other && colTime_other == -1) ==> grid[r][c_other] == 0
    {
      var rowVal, rowTime := row[i];
      var colVal, colTime := col[j];

      if rowTime == -1 && colTime == -1 {
        grid[i][j] := 0;
      } else if rowTime > colTime {
        grid[i][j] := rowVal;
      } else { // colTime > rowTime or colTime == rowTime (which implies one or both are not -1)
        grid[i][j] := colVal;
      }
    }
  }
  grid
}

function FormatGrid(grid: seq<seq<int>>): string
  requires |grid| > 0 && |grid[0]| > 0
  reads Ghost
{
  var result := "";
  for i := 0 to |grid|-1
    invariant 0 <= i <= |grid|
    invariant result == (if i == 0 then "" else FormatGrid(grid[0..i]))
    invariant forall k :: 0 <= k < i ==> result.Contains('\n') || k == 0
  {
    var rowString := "";
    for j := 0 to |grid[i]|-1
      invariant 0 <= j <= |grid[i]|
      invariant rowString == (if j == 0 then "" else FormatString(grid[i][0..j]))
      invariant forall k :: 0 <= k < j ==> rowString.Contains(' ') || k == 0
    {
      rowString := rowString + grid[i][j].ToString();
      if j < |grid[i]|-1 {
        rowString := rowString + " ";
      }
    }
    result := result + rowString;
    if i < |grid|-1 {
      result := result + "\n";
    }
  }
  result
}

function FormatString(s: seq<int>): string
  reads Ghost
{
  var result := "";
  for i := 0 to |s|-1
    invariant 0 <= i <= |s|
    invariant result == (if i == 0 then "" else FormatString(s[0..i]))
    invariant forall k :: 0 <= k < i ==> result.Contains(' ') || k == 0
  {
    result := result + s[i].ToString();
    if i < |s|-1 {
      result := result + " ";
    }
  }
  result
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
  if !ValidInput(input) {
    return "";
  }
  var (n, m, k) := GetDimensions(input);
  var lines := SplitLines(input);
  var grid := ComputeGrid(lines, n, m, k);
  return FormatGrid(grid);
}
// </vc-code>

