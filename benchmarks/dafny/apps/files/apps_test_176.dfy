Count the number of integers in the range [a, b] that are divisible by k.
Given three integers k, a, b where k > 0 and a <= b, return the count of
integers x such that a <= x <= b and x % k == 0.

predicate ValidInput(k: int, a: int, b: int)
{
  k > 0 && a <= b
}

function FloorDiv(a: int, b: int): int
  requires b > 0
{
  if a >= 0 then a / b
  else (a - b + 1) / b
}

function CountDivisiblesInRange(k: int, a: int, b: int): int
  requires k > 0
  requires a <= b
{
  FloorDiv(b, k) - FloorDiv(a - 1, k)
}

method solve(k: int, a: int, b: int) returns (result: int)
  requires ValidInput(k, a, b)
  ensures result >= 0
  ensures result == CountDivisiblesInRange(k, a, b)
{
  var s1 := FloorDiv(a - 1, k);
  var s2 := FloorDiv(b, k);
  result := s2 - s1;
  assert s2 >= s1;
}
