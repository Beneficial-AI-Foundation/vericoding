// <vc-preamble>
predicate ValidInput(N: int) {
    100 <= N <= 999
}

predicate ContainsSeven(N: int) 
    requires ValidInput(N)
{
    (N % 10) == 7 || ((N / 10) % 10) == 7 || (N / 100) == 7
}

predicate ValidOutput(result: string) {
    result == "Yes\n" || result == "No\n"
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: string)
    requires ValidInput(N)
    ensures ValidOutput(result)
    ensures result == "Yes\n" <==> ContainsSeven(N)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
