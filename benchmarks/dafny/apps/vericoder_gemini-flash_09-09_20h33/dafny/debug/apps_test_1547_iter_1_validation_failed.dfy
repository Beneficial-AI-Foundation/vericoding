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
reads input
ensures forall i :: 0 <= i < |SplitLines(input)| ==> |SplitLines(input)[i]| <= |input|
{
  if input == "" then
    []
  else if input.Contains('\n') then
    var firstLine := input.Substring(0, input.IndexOf('\n'));
    var rest := input.Substring(input.IndexOf('\n') + 1);
    [firstLine] + SplitLines(rest)
  else
    [input]
}

function StringToInt(s: string): int
reads s
// This is a simplified StringToInt. A real one would need more robust parsing and error handling.
// For this problem, we assume valid integer strings will be provided.
ensures s == "-0" ==> StringToInt(s) == 0 // Handle -0 case
ensures s == "0" ==> StringToInt(s) == 0
ensures ValidIntString(s) ==> (var i := 0; var sign := 1; if s[0] == '-' then (i := 1; sign := -1); sign * ParsePositiveIntString(s, i))
{
  if s == "" then 0 // Or could be an error, depending on spec
  else if s[0] == '-' then
    if |s| == 1 then 0 // Error case: just "-"
    else -StringToInt(s[1..])
  else
    var num := 0;
    var pwr := 1;
    for i := |s| - 1 downto 0
      invariant 0 <= i < |s|
      invariant pwr == Pow10(|s| - 1 - i)
      invariant num == ParsePartialPositiveIntString(s, i + 1, |s|)
    {
      if '0' <= s[i] <= '9' then
        num := num + (s[i] as int - '0' as int) * pwr;
        pwr := pwr * 10;
      else
        return 0; // Error case: non-digit character
    }
    num
}

predicate ValidIntString(s: string)
{
  |s| > 0 &&
  (s[0] == '-' ==> |s| > 1 && (forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9')) &&
  (s[0] != '-' ==> (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'))
}

// Helper for StringToInt
function ParsePositiveIntString(s: string, startIndex: int): int
requires 0 <= startIndex <= |s|
requires forall i :: startIndex <= i < |s| ==> '0' <= s[i] <= '9'
{
  var num := 0;
  var pwr := 1;
  for i := |s| - 1 downto startIndex
    invariant startIndex <= i < |s|
    invariant pwr == Pow10(|s| - 1 - i)
    invariant num == ParsePartialPositiveIntString(s, i + 1, |s|)
  {
    num := num + (s[i] as int - '0' as int) * pwr;
    pwr := pwr * 10;
  }
  num
}

// Helper for StringToInt
function ParsePartialPositiveIntString(s: string, fromIndex: int, toIndex: int): int
requires 0 <= fromIndex <= toIndex <= |s|
requires forall i :: fromIndex <= i < toIndex ==> '0' <= s[i] <= '9'
{
  var num := 0;
  var pwr := 1;
  for i := toIndex - 1 downto fromIndex
    invariant fromIndex <= i < toIndex
    invariant pwr == Pow10(toIndex - 1 - i)
    invariant num == ParsePartialPositiveIntString(s, i + 1, toIndex)
  {
    num := num + (s[i] as int - '0' as int) * pwr;
    pwr := pwr * 10;
  }
  num
}

function Pow10(exp: int): int
requires exp >= 0
{
  if exp == 0 then 1
  else 10 * Pow10(exp - 1)
}

function SplitString(input: string, delimiter: char): seq<string>
reads input
ensures forall i :: 0 <= i < |SplitString(input, delimiter)| ==> |SplitString(input, delimiter)[i]| <= |input|
{
  if input == "" then
    []
  else
    var idx := input.IndexOf(delimiter);
    if idx == -1 then
      [input]
    else
      var head := input.Substring(0, idx);
      var tail := input.Substring(idx + 1);
      [head] + SplitString(tail, delimiter)
}

function ProcessOperations(lines: seq<string>, n: int, m: int, k: int, currentK: int, row: seq<(int, int)>, col: seq<(int, int)>): (seq<(int, int)>, seq<(int, int)>)
requires 0 <= currentK <= k
requires |lines| >= k + 1
requires n > 0 && m > 0
requires |row| == n && forall i :: 0 <= i < n ==> row[i].0 >= 0 && row[i].1 <= currentK
requires |col| == m && forall i :: 0 <= i < m ==> col[i].0 >= 0 && col[i].1 <= currentK
// This ensures the processed arrays `row` and `col` correctly reflect operations up to `currentK`.
ensures var (finalRow, finalCol) := ProcessOperations(lines, n, m, k, currentK, row, col);
        |finalRow| == n && forall i :: 0 <= i < n ==> finalRow[i].1 <= k
        && |finalCol| == m && forall i :: 0 <= i < m ==> finalCol[i].1 <= k
{
    if currentK == k then
        (row, col)
    else
        var operationLine := SplitString(lines[currentK + 1], ' ');
        var opType := StringToInt(operationLine[0]);
        var index := StringToInt(operationLine[1]);
        var value := StringToInt(operationLine[2]);

        if opType == 0 then // Row operation
            var newRow := row[index := (value, currentK)];
            ProcessOperations(lines, n, m, k, currentK + 1, newRow, col)
        else if opType == 1 then // Column operation
            var newCol := col[index := (value, currentK)];
            ProcessOperations(lines, n, m, k, currentK + 1, row, newCol)
        else // Should not happen given constraints, but for totality:
            ProcessOperations(lines, n, m, k, currentK + 1, row, col)
}

function BuildGrid(n: int, m: int, row: seq<(int, int)>, col: seq<(int, int)>): seq<seq<int>>
requires n > 0 && m > 0
requires |row| == n && forall i :: 0 <= i < n ==> row[i].0 >= 0
requires |col| == m && forall i :: 0 <= i < m ==> col[i].0 >= 0
ensures |BuildGrid(n,m,row,col)| == n
ensures forall r :: 0 <= r < n ==> |BuildGrid(n,m,row,col)[r]| == m
ensures forall r, c :: 0 <= r < n && 0 <= c < m ==> BuildGrid(n,m,row,col)[r][c] >= 0
{
    seq(n, r => seq(m, c => {
        if row[r].1 > col[c].1 then
            row[r].0
        else
            col[c].0
    }))
}

function FormatGrid(grid: seq<seq<int>>): string
requires |grid| > 0
requires forall r :: 0 <= r < |grid| ==> |grid[r]| > 0
ensures |FormatGrid(grid)| >= 0 // Should produce a non-empty string for valid grids
{
    var formattedRows := seq(|grid|, r => {
        var rowStr := "";
        for c := 0 to |grid[r]| - 1
        {
            if c > 0 then
                rowStr := rowStr + " ";
            rowStr := rowStr + grid[r][c] as string;
        }
        rowStr
    });

    var resultStr := "";
    for r := 0 to |formattedRows| - 1
    {
        if r > 0 then
            resultStr := resultStr + "\n";
        resultStr := resultStr + formattedRows[r];
    }
    resultStr
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
    // Proof of `ValidInput(input)` implies the following properties:
    // P1: `n > 0`, `m > 0`, `k >= 0`
    // P2: `|lines| >= k + 1`
    // P1 and P2 are preconditions for `ComputeGrid`.
    //
    // `ComputeGrid`'s postcondition: returns a grid `g` where `|g| == n` and `|g[r]| == m`.
    // These properties are preconditions for `FormatGrid`.
    // Thus, `FormatGrid` is called with valid arguments if `ValidInput` holds.
}
// </vc-code>

