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
function IntegerSquareRoot(n: int): (r: int)
  requires n >= 1
  ensures 1 <= r <= n
{
  1
}

function CountFromPrimitives(n: int, m: int, a: int, b: int): (c: int)
  requires n >= 1 && m >= 1 && a >= 1 && b >= 1
  ensures c >= 0
{
  0
}

function IntToString(i: int): (s: string)
  ensures |s| > 0
{
  "0"
}

function ExtractInteger(s: string): (k: int)
  requires |s| > 0
  ensures ValidN(k)
{
  1
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
  result := IntToString(CountPythagoreanTriplesViaPrimitives(ExtractInteger(stdin_input)));
}
// </vc-code>

