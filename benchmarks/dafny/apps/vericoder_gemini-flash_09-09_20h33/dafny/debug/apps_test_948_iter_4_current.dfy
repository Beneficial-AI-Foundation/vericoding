predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidGrid(grid: seq<string>, n: int, m: int)
{
    n >= 1 && m >= 1 && |grid| == n &&
    forall i :: 0 <= i < |grid| ==> |grid[i]| == m
}

function CountFaceSquares(input: string): int
    requires |input| > 0
    ensures CountFaceSquares(input) >= 0
{
    var lines := SplitLinesFunc(input);
    if |lines| == 0 then 0
    else
        var firstLine := lines[0];
        var nm := SplitSpacesFunc(firstLine);
        if |nm| < 2 then 0
        else
            var n := StringToIntFunc(nm[0]);
            var m := StringToIntFunc(nm[1]);
            if n < 1 || m < 1 || |lines| < n + 1 then 0
            else
                var grid := lines[1..n+1];
                CountValidSquares(grid, n, m)
}

function CountFaceSquaresAsString(input: string): string
    requires |input| > 0
    ensures |CountFaceSquaresAsString(input)| > 0
{
    var count := CountFaceSquares(input);
    IntToStringFunc(count) + "\n"
}

// <vc-helpers>
function SplitLinesFunc(s: string): seq<string>
  ensures forall i :: 0 <= i < |SplitLinesFunc(s)| ==> |SplitLinesFunc(s)[i]| <= |s|
  ensures (s == "" || s == "\n") ==> |SplitLinesFunc(s)| == 0
{
  if s == "" then []
  else if s == "\n" then []
  else 
    var lines := [];
    var i := 0;
    var start := 0;
    while i < |s| 
      decreases |s| - i
      invariant 0 <= i <= |s|
      invariant 0 <= start <= i
      invariant forall k :: 0 <= k < |lines| ==> |lines[k]| <= |s|
    {
      if s[i] == '\n' {
        lines := lines + [s[start..i]];
        start := i + 1;
      }
      i := i + 1;
    }
    if start < |s| then
      lines + [s[start..|s|]]
    else
      lines
}

function SplitSpacesFunc(s: string): seq<string>
  ensures forall i :: 0 <= i < |SplitSpacesFunc(s)| ==> |SplitSpacesFunc(s)[i]| <= |s|
  ensures (s == "" || s == " ") ==> |SplitSpacesFunc(s)| == 0
{
  if s == "" then []
  else if s == " " then []
  else
    var parts := [];
    var i := 0;
    var start := 0;
    while i < |s| 
      decreases |s| - i
      invariant 0 <= i <= |s|
      invariant 0 <= start <= i
      invariant forall k :: 0 <= k < |parts| ==> |parts[k]| <= |s|
    {
      if s[i] == ' ' {
        if start < i {
          parts := parts + [s[start..i]];
        }
        start := i + 1;
      }
      i := i + 1;
    }
    if start < |s| then
      parts + [s[start..|s|]]
    else
      parts
}

function StringToIntFunc(s: string): int
  requires forall c :: c in s ==> '0' <= c <= '9'
  requires |s| > 0
  ensures StringToIntFunc(s) >= 0
{
  var n := 0;
  var i := 0;
  while i < |s| 
    decreases |s| - i
    invariant 0 <= i <= |s|
    invariant n >= 0
  {
    n := n * 10 + (s[i] as int - '0' as int);
    i := i + 1;
  }
  n
}

function IntToStringFunc(n: int): string
  requires n >= 0
  ensures |IntToStringFunc(n)| > 0 || n == 0
{
  if n == 0 then "0"
  else
    var s := "";
    var temp := n;
    while temp > 0
      decreases temp
      invariant temp >= 0
      invariant forall c :: c in s ==> '0' <= c <= '9'
    {
      s := (temp % 10 as char + '0' as char) + s;
      temp := temp / 10;
    }
    s
}

function CountValidSquares(grid: seq<string>, n: int, m: int): int
  requires ValidGrid(grid, n, m)
  ensures CountValidSquares(grid, n, m) >= 0
{
  var count := 0;
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant count >= 0
  {
    for j := 0 to m - 1
      invariant 0 <= j <= m
      invariant count >= 0
    {
      if grid[i][j] == 'X' then
        count := count + 1;
    }
  }
  count
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| > 0
    ensures result == CountFaceSquaresAsString(input)
// </vc-spec>
// <vc-code>
{
  result := CountFaceSquaresAsString(input);
}
// </vc-code>

