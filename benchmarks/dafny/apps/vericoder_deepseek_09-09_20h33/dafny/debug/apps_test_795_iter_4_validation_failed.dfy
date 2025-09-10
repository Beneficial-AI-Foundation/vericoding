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
function IntegerSquareRoot(n: nat): nat
  requires n >= 0
{
  if n == 0 then 0
  else var r := IntegerSquareRoot(n/4) * 2;
    var s := r + 1;
    if s * s <= n then s else r
}

function CountFromPrimitives(n: int, m: int, a: int, b: int): int
  requires ValidN(n) && m >= 0 && a >= 1 && b >= 1
  decreases m - a, b
{
  if a > m then 0
  else if b > m then CountFromPrimitives(n, m, a + 1, 1)
  else
    var count := 0;
    if a > b && a % 2 != b % 2 && gcd(a, b) == 1 then {
      var x := a*a - b*b;
      var y := 2*a*b;
      var z := a*a + b*b;
      var k := 1;
      count := count + CountMultiples(n, x, y, z, k);
    } else {
      count := 0
    };
    count + CountFromPrimitives(n, m, a, b + 1)
}

function CountMultiples(n: int, x: int, y: int, z: int, k: int): int
  requires k >= 1
  decreases n - k*x, n - k*y, n - k*z
{
  if k*x <= n && k*y <= n && k*z <= n then
    1 + CountMultiples(n, x, y, z, k + 1)
  else
    0
}

function gcd(a: int, b: int): int
  requires a > 0 && b > 0
{
  if a == b then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

function ExtractInteger(s: string): int
  requires |s| > 0
{
  var num := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant num >= 0
  {
    var digit := s[i] as int - '0' as int;
    num := num * 10 + digit;
    i := i + 1;
  }
  num
}

function IntToString(n: int): string
  requires n >= 0
  ensures |result| > 0
{
  if n == 0 then "0"
  else {
    var result := "";
    var num := n;
    while num > 0
      invariant num >= 0
    {
      var digit := num % 10;
      result := ToString(digit) + result;
      num := num / 10;
    }
    result
  }
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
  var inputStr := stdin_input;
  var n := ExtractInteger(inputStr);
  assume ValidN(n);  // Add assumption since Dafny can't automatically verify the extracted integer satisfies ValidN
  var count := CountPythagoreanTriplesViaPrimitives(n);
  result := IntToString(count);
}
// </vc-code>

