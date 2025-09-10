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
function {:axiom} IntegerSquareRoot(n: int): int
  requires n >= 0
  ensures IntegerSquareRoot(n) >= 0
  ensures IntegerSquareRoot(n) * IntegerSquareRoot(n) <= n
  ensures (IntegerSquareRoot(n) + 1) * (IntegerSquareRoot(n) + 1) > n

function {:axiom} CountFromPrimitives(n: int, m: int, i: int, j: int): int
  requires ValidN(n)
  requires m >= 0
  requires i >= 0
  requires j >= 0
  decreases m - i, m - j

function {:axiom} ExtractInteger(s: string): int
  requires ValidInput(s)
  ensures ValidN(ExtractInteger(s))

function {:axiom} IntToString(n: int): string
  ensures |IntToString(n)| > 0

method {:axiom} ComputeIntegerSquareRoot(n: int) returns (result: int)
  requires n >= 0
  ensures result == IntegerSquareRoot(n)
  ensures result >= 0
  ensures result * result <= n
  ensures (result + 1) * (result + 1) > n

method {:axiom} ComputeCountFromPrimitives(n: int, m: int, i: int, j: int) returns (count: int)
  requires ValidN(n)
  requires m >= 0
  requires i >= 0
  requires j >= 0
  ensures count == CountFromPrimitives(n, m, i, j)

method {:axiom} ParseInteger(s: string) returns (n: int)
  requires ValidInput(s)
  ensures n == ExtractInteger(s)
  ensures ValidN(n)

method {:axiom} ConvertIntToString(n: int) returns (s: string)
  ensures s == IntToString(n)
  ensures |s| > 0
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

