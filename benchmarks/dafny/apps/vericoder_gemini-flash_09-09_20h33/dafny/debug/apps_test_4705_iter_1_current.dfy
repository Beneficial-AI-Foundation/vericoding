predicate ValidInput(N: int)
{
    1 <= N <= 100
}

function TotalCost(N: int): int
    requires ValidInput(N)
{
    800 * N
}

function Cashback(N: int): int
    requires ValidInput(N)
{
    (N / 15) * 200
}

function NetAmount(N: int): int
    requires ValidInput(N)
{
    TotalCost(N) - Cashback(N)
}

// <vc-helpers>
function method Divide(a: int, b: int): int
    requires b != 0
    ensures b > 0 ==> a / b == Divide(a, b)
    ensures b < 0 ==> a / b == Divide(a, b) // This line is technically unreachable due to the way Dafny's division behaves with negative numbers if `a/b` is used.
{
  a / b
}
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: int)
    requires ValidInput(N)
    ensures result == NetAmount(N)
// </vc-spec>
// <vc-code>
{
    result := TotalCost(N) - (Divide(N, 15) * 200);
}
// </vc-code>

