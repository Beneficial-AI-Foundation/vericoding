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
    var lines: seq<string> := [];
    var startIndex := 0;
    var i := 0;
    while i < |input|
      invariant 0 <= i <= |input|
      invariant 0 <= startIndex <= i
      invariant forall j :: 0 <= j < |lines| ==> lines[j].IsWellFormedString()
      invariant input[0..i].IsWellFormedString()
    {
      if input[i] == '\n' {
        lines := lines + [input[startIndex..i]];
        startIndex := i + 1;
      }
      i := i + 1;
    }
    // Add the last line after the loop
    lines := lines + [input[startIndex..|input|]];
    lines
}

function SplitString(input: string, delimiter: char): seq<string>
  reads Ghost
{
  if input == "" then
      []
  else
    var result: seq<string> := [];
    var startIndex := 0;
    var i := 0;
    while i < |input|
      invariant 0 <= i <= |input|
      invariant 0 <= startIndex <= i
      invariant forall j :: 0 <= j < |result| ==> result[j].IsWellFormedString()
      invariant input[0..i].IsWellFormedString()
    {
      if input[i] == delimiter {
        result := result + [input[startIndex..i]];
        startIndex := i + 1;
      }
      i := i + 1;
    }
    // Add the last part after the loop
    result := result + [input[startIndex..|input|]];
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
    invariant (forall k :: (if sign == 1 then 0 else 1) <= k < i ==> '0' <= s[k] <= '9')
    invariant s[0..i].IsWellFormedString()
  {
    if '0' <= s[i] <= '9' {
      num := num * 10 + (s[i] as int - '0' as int);
    } else {
      // This case should ideally not be reached if the input string is guaranteed to be a valid integer.
      // For robustness, one might return an error or a special value, but for competitive programming,
      // usually inputs are well-formed. Assert(false) is fine for now assuming valid input.
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
    invariant forall r_pred :: 0 <= r_pred < i ==>
      (forall c_pred :: 0 <= c_pred < m ==>
        var rowVal_pred, rowTime_pred := row[r_pred];
        var colVal_pred, colTime_pred := col[c_pred];
        (if rowTime_pred > colTime_pred then grid[r_pred][c_pred] == rowVal_pred
         else if colTime_pred > rowTime_pred then grid[r_pred][c_pred] == colVal_pred
         else if rowTime_pred == -1 then grid[r_pred][c_pred] == 0
         else grid[r_pred][c_pred] == rowVal_pred
        )
      )
  {
    for j := 0 to m-1
      invariant 0 <= j <= m
      invariant |grid| == n
      invariant |grid[i]| == m
      invariant forall c_pred :: 0 <= c_pred < j ==>
        var rowVal_i, rowTime_i := row[i];
        var colVal_pred, colTime_pred := col[c_pred];
        (if rowTime_i > colTime_pred then grid[i][c_pred] == rowVal_i
         else if colTime_pred > rowTime_i then grid[i][c_pred] == colVal_pred
         else if rowTime_i == -1 then grid[i][c_pred] == 0
         else grid[i][c_pred] == rowVal_i
        )
      invariant forall r_pred :: 0 <= r_pred < i ==>
        (forall c_other :: 0 <= c_other < m ==>
          var rowVal_pred, rowTime_pred := row[r_pred];
          var colVal_other, colTime_other := col[c_other];
          (if rowTime_pred > colTime_other then grid[r_pred][c_other] == rowVal_pred
           else if colTime_other > rowTime_pred then grid[r_pred][c_other] == colVal_other
           else if rowTime_pred == -1 then grid[r_pred][c_other] == 0
           else grid[r_pred][c_other] == rowVal_pred
          )
        )
    {
      var rowVal, rowTime := row[i];
      var colVal, colTime := col[j];

      if rowTime > colTime {
        grid[i][j] := rowVal;
      } else if colTime > rowTime {
        grid[i][j] := colVal;
      } else { // colTime == rowTime
        if rowTime == -1 { // Both are -1, so it means no operation happened, default to 0
          grid[i][j] := 0;
        } else { // colTime == rowTime and not -1, row operation takes precedence
          grid[i][j] := rowVal;
        }
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
    invariant result.IsWellFormedString()
    invariant (if i == 0 then result == "" else true)
    invariant forall k :: 0 <= k < i ==> "\n" in result
  {
    var rowString := "";
    for j := 0 to |grid[i]|-1
      invariant 0 <= j <= |grid[i]|
      invariant rowString.IsWellFormedString()
      invariant (if j == 0 then rowString == "" else true)
      invariant forall k :: 0 <= k < j ==> " " in rowString
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
// This helper function is unused but required in the original code.
function FormatString(s: seq<int>): string
  reads Ghost
{
  var result := "";
  for i := 0 to |s|-1
    invariant 0 <= i <= |s|
    invariant result.IsWellFormedString()
    invariant (if i==0 then result=="" else true)
    invariant forall k :: 0 <= k < i ==> " " in result
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

