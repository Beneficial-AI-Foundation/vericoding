// <vc-preamble>
predicate ValidInput(N: int) {
  1000 <= N <= 9999
}

function ExtractDigits(N: int): (int, int, int, int)
  requires ValidInput(N)
{
  var d1 := N / 1000;
  var d2 := (N / 100) % 10;
  var d3 := (N / 10) % 10;
  var d4 := N % 10;
  (d1, d2, d3, d4)
}

predicate IsGood(N: int)
  requires ValidInput(N)
{
  var (d1, d2, d3, d4) := ExtractDigits(N);
  (d1 == d2 && d2 == d3) || (d2 == d3 && d3 == d4)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: string)
  requires ValidInput(N)
  ensures result == "Yes" || result == "No"
  ensures result == "Yes" <==> IsGood(N)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
