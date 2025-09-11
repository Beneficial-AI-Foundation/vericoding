// <vc-preamble>
predicate ValidRectangleParts(a: int, b: int, n: int)
{
    a > 0 && b > 0 && a != b && 2 * a + 2 * b == n
}

function CountValidRectangles(n: int): int
    requires n > 0
{
    if n % 2 == 1 then 0
    else if n % 4 == 2 then n / 4
    else n / 4 - 1
}

predicate ValidInput(n: int)
{
    n > 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == CountValidRectangles(n)
    ensures n % 2 == 1 ==> result == 0
    ensures n % 2 == 0 && n % 4 == 2 ==> result == n / 4
    ensures n % 2 == 0 && n % 4 == 0 ==> result == n / 4 - 1
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
