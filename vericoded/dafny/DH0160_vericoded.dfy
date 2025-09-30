// <vc-preamble>

predicate ValidInput(number: int, need: int, remaining: int)
{
    0 <= number <= 1000 && 0 <= need <= 1000 && 0 <= remaining <= 1000
}

function CanEat(need: int, remaining: int): int
{
    if need <= remaining then need else remaining
}

function TotalEaten(number: int, need: int, remaining: int): int
{
    number + CanEat(need, remaining)
}

function CarrotsLeft(need: int, remaining: int): int
{
    remaining - CanEat(need, remaining)
}

predicate ValidResult(result: seq<int>, number: int, need: int, remaining: int)
{
    |result| == 2 &&
    result[0] == TotalEaten(number, need, remaining) &&
    result[1] == CarrotsLeft(need, remaining) &&
    result[0] >= number &&
    result[1] >= 0 &&
    result[1] <= remaining
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method eat(number: int, need: int, remaining: int) returns (result: seq<int>)
    requires ValidInput(number, need, remaining)
    ensures ValidResult(result, number, need, remaining)
// </vc-spec>
// <vc-code>
{
  var eaten := if need <= remaining then need else remaining;
  result := [number + eaten, remaining - eaten];
}
// </vc-code>
