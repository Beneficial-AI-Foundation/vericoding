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
function gcd(a: int, b: int): int
  requires a > 0 && b > 0
{
  if b == 0 then a
  else gcd(b, a % b)
}

function IntegerSquareRoot(n: int): int
  requires n >= 0
{
  if n == 0 then 0
  else IntegerSquareRootHelper(n, 1, n)
}

function IntegerSquareRootHelper(n: int, low: int, high: int): int
  decreases high - low
{
  if low > high then 0
  var mid := (low + high) / 2;
  if mid * mid <= n && (mid + 1) * (mid + 1) > n then mid
  else if mid * mid > n then IntegerSquareRootHelper(n, low, mid - 1)
  else IntegerSquareRootHelper(n, mid + 1, high)
}

function CountFromPrimitives(n: int, m: int, u: int, v: int): int
{
  if u > m then 0
  else if v >= u then CountFromPrimitives(n, m, u+1, 1)
  else if v % 2 != u % 2 && gcd(u, v) == 1 then
    var c := u*u + v*v;
    if c <= n then 1 + CountFromPrimitives(n, m, u, v+2)
    else CountFromPrimitives(n, m, u, v+2)
  else CountFromPrimitives(n, m, u, v+1)
}

function IntToString(n: int): string
  decreases n
{
  if n == 0 then "0"
  else IntToString(n / 10) + [n % 10 + 48 as char]
}

function method ExtractInteger(s: string): int
  requires ValidInput(s)
  ensures ValidN(ExtractInteger(s))
{
  var num  := 0;
  var i := 0;
  while i < |s|
    invariant i <= |s|
    decreases |s| - i
    invariant num >= 0
  {
    var digit := (s[i] as int) - 48;
    assert 0 <= digit <= 9;
    num := num * 10 + digit;
    i := i + 1;
  }
  assert 1 <= num <= 10000;
  num
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
  var n := ExtractInteger(stdin_input);
  var count := CountPythagoreanTriplesViaPrimitives(n);
  result := IntToString(count);
}
// </vc-code>

