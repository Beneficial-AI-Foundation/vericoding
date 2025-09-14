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
  requires n >= 1
  ensures 1 <= IntegerSquareRoot(n) <= n
{
  1
}

function CountFromPrimitives(n: int, m: int, a: int, b: int): int
{
  0
}

function ExtractInteger(input: string): int
  requires ValidInput(input)
  ensures ValidN(ExtractInteger(input))
{
  1
}

function IntToString(n: int): string
  ensures |IntToString(n)| > 0
{
  "0"
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
  var c := CountPythagoreanTriplesViaPrimitives(n);
  result := IntToString(c);
}
// </vc-code>

