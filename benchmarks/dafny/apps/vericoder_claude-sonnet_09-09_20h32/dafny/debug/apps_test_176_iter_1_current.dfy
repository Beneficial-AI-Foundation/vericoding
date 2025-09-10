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

// <vc-helpers>
lemma FloorDivProperties(a: int, b: int)
  requires b > 0
  ensures FloorDiv(a, b) * b <= a < (FloorDiv(a, b) + 1) * b
{
  if a >= 0 {
    assert FloorDiv(a, b) == a / b;
  } else {
    assert FloorDiv(a, b) == (a - b + 1) / b;
  }
}

lemma CountDivisiblesNonNegative(k: int, a: int, b: int)
  requires k > 0
  requires a <= b
  ensures CountDivisiblesInRange(k, a, b) >= 0
{
  assert FloorDiv(b, k) >= FloorDiv(a - 1, k);
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, a: int, b: int) returns (result: int)
  requires ValidInput(k, a, b)
  ensures result >= 0
  ensures result == CountDivisiblesInRange(k, a, b)
// </vc-spec>
// <vc-code>
{
  var floorB := FloorDiv(b, k);
  var floorA := FloorDiv(a - 1, k);
  result := floorB - floorA;
  
  CountDivisiblesNonNegative(k, a, b);
}
// </vc-code>

