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
function IntToString(i: int): string {
  "x"
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
  var res: seq<string> := [IntToString(MaxCoders(n))];
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant |res| == i
    invariant res[0] == IntToString(MaxCoders(n))
    invariant forall k :: 1 <= k < i ==> |res[k]| == n
    invariant forall k :: 1 <= k < i ==> forall j :: 0 <= j < n ==>
      (res[k][j] == 'C' <==> (if (k - 1) % 2 == 0 then j % 2 == 0 else j % 2 == 1))
    decreases n + 1 - i
  {
    var row: string := "";
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |row| == j
      invariant forall c :: 0 <= c < j ==>
        (row[c] == 'C' <==> (if (i - 1) % 2 == 0 then c % 2 == 0 else c % 2 == 1))
      decreases n - j
    {
      if ((i - 1) % 2 == 0) {
        if j % 2 == 0 {
          row := row + ['C'];
        } else {
          row := row + ['.'];
        }
      } else {
        if j % 2 == 1 {
          row := row + ['C'];
        } else {
          row := row + ['.'];
        }
      }
      j := j + 1;
    }
    res := res + [row];
    i := i + 1;
  }
  result := res;
}
// </vc-code>

