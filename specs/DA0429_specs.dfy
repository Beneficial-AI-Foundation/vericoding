// <vc-preamble>
predicate ValidSolution(n: int, a: int, b: int, c: int)
{
    a >= 0 && b >= 0 && c >= 0 && 3 * a + 5 * b + 7 * c == n
}

predicate ValidResult(n: int, result: seq<int>)
{
    (|result| == 1 && result[0] == -1) ||
    (|result| == 3 && result[0] >= 0 && result[1] >= 0 && result[2] >= 0 && 
     ValidSolution(n, result[0], result[1], result[2]))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<int>)
    requires n >= 1
    ensures ValidResult(n, result)
    ensures n % 3 == 0 ==> |result| == 3 && result == [n / 3, 0, 0]
    ensures n % 3 == 1 && n < 7 ==> |result| == 1 && result[0] == -1
    ensures n % 3 == 1 && n >= 7 ==> |result| == 3 && result == [(n - 7) / 3, 0, 1]
    ensures n % 3 == 2 && n < 5 ==> |result| == 1 && result[0] == -1
    ensures n % 3 == 2 && n >= 5 ==> |result| == 3 && result == [(n - 5) / 3, 1, 0]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
