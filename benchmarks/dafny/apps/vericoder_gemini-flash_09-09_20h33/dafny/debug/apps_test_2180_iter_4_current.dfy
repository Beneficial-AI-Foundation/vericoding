predicate ValidInput(n: int) {
    n >= 1
}

function MaxCoders(n: int): int
    requires n >= 1
{
    n * n / 2 + n * n % 2
}

predicate ValidOutputFormat(result: seq<string>, n: int) 
    requires n >= 1
{
    |result| == n + 1 &&
    result[0] == IntToString(MaxCoders(n)) &&
    (forall i :: 1 <= i <= n ==> |result[i]| == n)
}

predicate ValidCheckerboardPlacement(result: seq<string>, n: int)
    requires n >= 1
    requires ValidOutputFormat(result, n)
{
    forall i :: 1 <= i <= n ==> forall j :: 0 <= j < n ==>
        (result[i][j] == 'C' <==> 
            (if (i - 1) % 2 == 0 then j % 2 == 0 else j % 2 == 1))
}

// <vc-helpers>
function IntToString(n: int): string
  requires n >= 0
  ensures (n == 0) == (|IntToString(n)| == 1 && IntToString(n)[0] == '0')
  ensures (n > 0) ==> (IntToString(n)[0] != '0')
{
  if n == 0 then
    "0"
  else
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      decreases temp
    {
      s := (temp % 10 as char) + '0' + s;
      temp := temp / 10;
    }
    s
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<string>)
    requires ValidInput(n)
    ensures ValidOutputFormat(result, n)
    ensures ValidCheckerboardPlacement(result, n)
// </vc-spec>
// <vc-code>
{
  var board: seq<string> := [];

  // Add the first element, which is MaxCoders(n) as string
  board := board + [IntToString(MaxCoders(n))];

  // Construct the checkerboard rows
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant |board| == i + 1
    invariant forall k :: 0 <= k < i ==> |board[k+1]| == n // rows added so far
    invariant forall r :: 0 <= r < i ==> forall c :: 0 <= c < n ==>
                (board[r+1][c] == 'C' <==> (if r % 2 == 0 then c % 2 == 0 else c % 2 == 1))
  {
    var row_str: string := "";
    for j := 0 to n - 1
      invariant 0 <= j <= n
      invariant |row_str| == j
      invariant forall k :: 0 <= k < j ==> (row_str[k] == 'C' <==> (if i % 2 == 0 then k % 2 == 0 else k % 2 == 1))
    {
      if i % 2 == 0 then
        // Even row (0-indexed): 'C' at even columns, '.' at odd columns
        if j % 2 == 0 then
          row_str := row_str + ['C'];
        else
          row_str := row_str + ['.'];
      else
        // Odd row (0-indexed): 'C' at odd columns, '.' at even columns
        if j % 2 == 1 then
          row_str := row_str + ['C'];
        else
          row_str := row_str + ['.'];
    }
    board := board + [row_str];
  }
  result := board;
}
// </vc-code>

