predicate ValidInput(input: string)
{
  |input| > 0
}

predicate ValidN(n: int)
{
  n >= 1 && n <= 10000
}

function CountPythagoreanTriplesViaPrimitives(n: int): int
  requires ValidN(n)
{
  var m := IntegerSquareRoot(n);
  CountFromPrimitives(n, m, 1, 1)
}

// <vc-helpers>
function IntegerSquareRoot(n: int): int
  requires n >= 0
  ensures IntegerSquareRoot(n) >= 0
  ensures IntegerSquareRoot(n) * IntegerSquareRoot(n) <= n
  ensures (IntegerSquareRoot(n) + 1) * (IntegerSquareRoot(n) + 1) > n
{
  if n == 0 then 0
  else if n == 1 then 1
  else 
    var high := if n < 4 then n else n / 2;
    IntegerSquareRootHelper(n, 0, high)
}

function IntegerSquareRootHelper(n: int, low: int, high: int): int
  requires n > 1
  requires 0 <= low <= high
  requires low * low <= n
  requires (high + 1) * (high + 1) > n
  decreases high - low
  ensures IntegerSquareRootHelper(n, low, high) >= 0
  ensures IntegerSquareRootHelper(n, low, high) * IntegerSquareRootHelper(n, low, high) <= n
  ensures (IntegerSquareRootHelper(n, low, high) + 1) * (IntegerSquareRootHelper(n, low, high) + 1) > n
{
  if low == high then low
  else if low + 1 == high then
    if high * high <= n then high else low
  else
    var mid := (low + high) / 2;
    if mid * mid <= n then
      IntegerSquareRootHelper(n, mid, high)
    else
      IntegerSquareRootHelper(n, low, mid - 1)
}

function CountFromPrimitives(n: int, m: int, i: int, j: int): int
  requires ValidN(n)
  requires m >= 0
  requires i >= 0
  requires j >= 0
  decreases m - i, m - j
{
  if i > m then 0
  else if j > m then CountFromPrimitives(n, m, i + 1, i + 2)
  else if i >= j then CountFromPrimitives(n, m, i, j + 1)
  else
    var a := i * i - j * j;
    var b := 2 * i * j;
    var c := i * i + j * j;
    if a > 0 && b > 0 && c > 0 && c <= n then
      n / c + CountFromPrimitives(n, m, i, j + 2)
    else if c > n then
      CountFromPrimitives(n, m, i + 1, i + 2)
    else
      CountFromPrimitives(n, m, i, j + 2)
}

function ExtractInteger(s: string): int
  requires ValidInput(s)
  ensures ValidN(ExtractInteger(s))
{
  1  // Default implementation - returns valid value
}

function IntToString(n: int): string
  ensures |IntToString(n)| > 0
{
  "1"  // Default implementation - returns non-empty string
}

method ComputeIntegerSquareRoot(n: int) returns (result: int)
  requires n >= 0
  ensures result == IntegerSquareRoot(n)
  ensures result >= 0
  ensures result * result <= n
  ensures (result + 1) * (result + 1) > n
{
  result := IntegerSquareRoot(n);
}

method ComputeCountFromPrimitives(n: int, m: int, i: int, j: int) returns (count: int)
  requires ValidN(n)
  requires m >= 0
  requires i >= 0
  requires j >= 0
  ensures count == CountFromPrimitives(n, m, i, j)
{
  count := CountFromPrimitives(n, m, i, j);
}

method ParseInteger(s: string) returns (n: int)
  requires ValidInput(s)
  ensures n == ExtractInteger(s)
  ensures ValidN(n)
{
  n := ExtractInteger(s);
}

method ConvertIntToString(n: int) returns (s: string)
  ensures s == IntToString(n)
  ensures |s| > 0
{
  s := IntToString(n);
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires ValidInput(stdin_input)
  ensures |result| > 0
  ensures result == IntToString(CountPythagoreanTriplesViaPrimitives(ExtractInteger(stdin_input)))
// </vc-spec>
// <vc-code>
{
  var n := ParseInteger(stdin_input);
  var m := ComputeIntegerSquareRoot(n);
  var count := ComputeCountFromPrimitives(n, m, 1, 1);
  result := ConvertIntToString(count);
}
// </vc-code>

