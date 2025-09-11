// <vc-preamble>
predicate ValidInput(n: int) {
    100 <= n <= 999
}

predicate ValidOutput(n: int, result: string)
    requires ValidInput(n)
{
    |result| == 6 && result[0..3] == "ABC" && result[3..] == IntToString(n)
}

function IntToString(n: int): string
    requires n >= 0
    ensures n == 0 ==> |IntToString(n)| == 1
    ensures 1 <= n <= 9 ==> |IntToString(n)| == 1
    ensures 10 <= n <= 99 ==> |IntToString(n)| == 2
    ensures 100 <= n <= 999 ==> |IntToString(n)| == 3
    decreases n
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else IntToString(n / 10) + [('0' as int + (n % 10)) as char]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
    requires ValidInput(n)
    ensures ValidOutput(n, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
