/*
Given A animals that are definitely cats and B animals of unknown type (could be cats or dogs),
determine if it's possible to have exactly X cats in total among the A + B animals.
*/

predicate ValidInput(a: int, b: int, x: int)
{
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= x <= 200
}

predicate CanHaveExactlyCats(a: int, b: int, x: int)
{
    a <= x <= a + b
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, x: int) returns (result: string)
    requires ValidInput(a, b, x)
    ensures result == "YES" <==> CanHaveExactlyCats(a, b, x)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
