Calculate the net amount paid by a customer for N meals at a restaurant.
Each meal costs 800 yen. For every 15 meals ordered, the customer receives
200 yen cashback. Return the net amount (total cost minus cashback).

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

method solve(N: int) returns (result: int)
    requires ValidInput(N)
    ensures result == NetAmount(N)
{
    var totalCost := 800 * N;
    var cashback := (N / 15) * 200;
    result := totalCost - cashback;
}
