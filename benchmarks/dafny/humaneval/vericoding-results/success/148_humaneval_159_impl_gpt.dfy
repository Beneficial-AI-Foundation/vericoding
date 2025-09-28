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
  } else {
    assert CanEat(need, remaining) == remaining;
  }
}

lemma CarrotsLeftBounds(need: int, remaining: int)
    requires 0 <= need && 0 <= remaining
    ensures 0 <= CarrotsLeft(need, remaining)
    ensures CarrotsLeft(need, remaining) <= remaining
{
  CanEatBounds(need, remaining);
  assert CarrotsLeft(need, remaining) == remaining - CanEat(need, remaining);
  var c := CanEat(need, remaining);
  assert 0 <= c;
  assert c <= remaining;
  assert 0 <= remaining - c;
  assert remaining - c <= remaining;
}

lemma TotalEatenLowerBound(number: int, need: int, remaining: int)
    requires 0 <= need && 0 <= remaining
    ensures number <= TotalEaten(number, need, remaining)
{
  CanEatBounds(need, remaining);
  var c := CanEat(need, remaining);
  assert 0 <= c;
  assert TotalEaten(number, need, remaining) == number + c;
  assert number <= number + c;
}
// </vc-helpers>

// <vc-spec>
method eat(number: int, need: int, remaining: int) returns (result: seq<int>)
    requires ValidInput(number, need, remaining)
    ensures ValidResult(result, number, need, remaining)
// </vc-spec>
// <vc-code>
{
  var eaten := TotalEaten(number, need, remaining);
  var left := CarrotsLeft(need, remaining);
  result := [eaten, left];
  CanEatBounds(need, remaining);
  CarrotsLeftBounds(need, remaining);
  TotalEatenLowerBound(number, need, remaining);
}
// </vc-code>
