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
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
method solve(k: int, a: int, b: int) returns (result: int)
  requires ValidInput(k, a, b)
  ensures result >= 0
  ensures result == CountDivisiblesInRange(k, a, b)
// </vc-spec>
// <vc-code>
{
  var countUpToB := if b >= 0 then b / k else (b - k + 1) / k;
  var countUpToAMinus1 := if a - 1 >= 0 then (a - 1) / k else ((a - 1) - k + 1) / k;
  result := countUpToB - countUpToAMinus1;
}
// </vc-code>

