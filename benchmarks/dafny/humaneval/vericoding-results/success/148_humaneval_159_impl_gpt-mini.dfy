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
lemma CanEatBounds(need: int, remaining: int)
  requires 0 <= need && 0 <= remaining
  ensures 0 <= CanEat(need, remaining)
  ensures CanEat(need, remaining) <= need
  ensures CanEat(need, remaining) <= remaining
{
  if need <= remaining {
    assert CanEat(need, remaining) == need;
    assert 0 <= need;
  } else {
    assert CanEat(need, remaining) == remaining;
    assert 0 <= remaining;
  }
}
// </vc-helpers>

// <vc-spec>
method eat(number: int, need: int, remaining: int) returns (result: seq<int>)
    requires ValidInput(number, need, remaining)
    ensures ValidResult(result, number, need, remaining)
// </vc-spec>
// <vc-code>
{
  var ce := CanEat(need, remaining);
  var total := number + ce;
  var left := remaining - ce;
  result := [total, left];
}
// </vc-code>
