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
{
  "0"
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
  var arr := new string[n + 1];
  arr[0] := IntToString(MaxCoders(n));
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant arr[0] == IntToString(MaxCoders(n))
    invariant forall r :: 1 <= r < i ==> |arr[r]| == n
    invariant forall r :: 1 <= r < i ==> forall j :: 0 <= j < n ==>
      (arr[r][j] == 'C' <==> (if (r - 1) % 2 == 0 then j % 2 == 0 else j % 2 == 1))
  {
    var row := "";
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |row| == j
      invariant forall k :: 0 <= k < j ==>
        (row[k] == 'C' <==> (if (i - 1) % 2 == 0 then k % 2 == 0 else k % 2 == 1))
    {
      if (i - 1) % 2 == 0 {
        if j % 2 == 0 {
          row := row + "C";
        } else {
          row := row + ".";
        }
      } else {
        if j % 2 == 1 {
          row := row + "C";
        } else {
          row := row + ".";
        }
      }
      j := j + 1;
    }
    arr[i] := row;
    i := i + 1;
  }
  result := arr[..];
}
// </vc-code>

