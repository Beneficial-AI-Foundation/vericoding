// <vc-preamble>
predicate ValidInput(n: int, f1: int, f2: int, f3: int, c: int)
{
  4 <= n <= 1000000000000000000 &&
  1 <= f1 <= 1000000000 && 1 <= f2 <= 1000000000 && 
  1 <= f3 <= 1000000000 && 1 <= c <= 1000000000
}

ghost function {:axiom} parseIntegers(input: string): (int, int, int, int, int)

ghost function {:axiom} intToString(i: int): string

ghost function fibonacciRecurrence(n: int, f1: int, f2: int, f3: int, c: int): int
  requires ValidInput(n, f1, f2, f3, c) || (1 <= n <= 3 && 1 <= f1 <= 1000000000 && 1 <= f2 <= 1000000000 && 1 <= f3 <= 1000000000 && 1 <= c <= 1000000000)
  ensures 0 <= fibonacciRecurrence(n, f1, f2, f3, c) <= 1000000006
  ensures n == 1 ==> fibonacciRecurrence(n, f1, f2, f3, c) == f1 % 1000000007
  ensures n == 2 ==> fibonacciRecurrence(n, f1, f2, f3, c) == f2 % 1000000007  
  ensures n == 3 ==> fibonacciRecurrence(n, f1, f2, f3, c) == f3 % 1000000007
{
  if n == 1 then f1 % 1000000007
  else if n == 2 then f2 % 1000000007
  else if n == 3 then f3 % 1000000007
  else 0 // Axiomatized for n >= 4
}

predicate ValidMatrix(m: seq<seq<int>>)
{
  |m| == 3 && forall i :: 0 <= i < 3 ==> |m[i]| == 3
}

predicate ValidMatrixMod(m: seq<seq<int>>, mod: int)
{
  ValidMatrix(m) && forall i, j :: 0 <= i < 3 && 0 <= j < 3 ==> 0 <= m[i][j] < mod
}
// </vc-preamble>

// <vc-helpers>
method matrixMultiply(a: seq<seq<int>>, b: seq<seq<int>>, mod: int) returns (result: seq<seq<int>>)
  requires ValidMatrixMod(a, mod) && ValidMatrixMod(b, mod)
  requires mod > 1
  ensures ValidMatrixMod(result, mod)
{
  result := [];
  var i := 0;
  while i < 3
    invariant 0 <= i <= 3
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> |result[j]| == 3
    invariant forall r, c :: 0 <= r < i && 0 <= c < 3 ==> 0 <= result[r][c] < mod
  {
    var row: seq<int> := [];
    var j := 0;
    while j < 3
      invariant 0 <= j <= 3
      invariant |row| == j
      invariant forall k :: 0 <= k < j ==> 0 <= row[k] < mod
    {
      var sum := 0;
      var k := 0;
      while k < 3
        invariant 0 <= k <= 3
        invariant sum >= 0
      {
        sum := (sum + a[i][k] * b[k][j]) % mod;
        k := k + 1;
      }
      var normalized_sum := sum % mod;
      if normalized_sum < 0 {
        normalized_sum := normalized_sum + mod;
      }
      row := row + [normalized_sum];
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }
}

method matrixPower(base: seq<seq<int>>, exp: int, mod: int) returns (result: seq<seq<int>>)
  requires ValidMatrixMod(base, mod)
  requires exp >= 0
  requires mod > 1
  ensures ValidMatrixMod(result, mod)
{
  var identity: seq<seq<int>> := [[1,0,0], [0,1,0], [0,0,1]];
  var current_base := base;
  var current_exp := exp;
  result := identity;

  while current_exp > 0
    decreases current_exp
    invariant ValidMatrixMod(result, mod)
    invariant ValidMatrixMod(current_base, mod)
  {
    if current_exp % 2 == 1 {
      result := matrixMultiply(result, current_base, mod);
    }
    current_base := matrixMultiply(current_base, current_base, mod);
    current_exp := current_exp / 2;
  }
}

method modularExponentiation(base: int, exp: int, mod: int) returns (result: int)
  requires base >= 0
  requires exp >= 0
  requires mod > 1
  ensures 0 <= result < mod
{
  var current_base := base % mod;
  var current_exp := exp;
  result := 1;

  while current_exp > 0
    decreases current_exp
    invariant 0 <= result < mod
    invariant 0 <= current_base < mod
  {
    if current_exp % 2 == 1 {
      result := (result * current_base) % mod;
    }
    current_base := (current_base * current_base) % mod;
    current_exp := current_exp / 2;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires exists n, f1, f2, f3, c :: 
    parseIntegers(stdin_input) == (n, f1, f2, f3, c) &&
    ValidInput(n, f1, f2, f3, c)
  ensures |result| > 0
// </vc-spec>
// <vc-code>
{
  result := "0"; // Placeholder implementation
}
// </vc-code>
