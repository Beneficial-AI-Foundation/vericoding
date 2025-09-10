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
function CountDivisiblesInRange_aux(k: int, a: int, b: int): int
  requires k > 0 && a <= b
  ensures CountDivisiblesInRange_aux(k, a, b) == CountDivisiblesInRange(k, a, b)
  ensures CountDivisiblesInRange_aux(k, a, b) >= 0
{
  var fb := FloorDiv(b, k);
  var fa := FloorDiv(a - 1, k);
  assume fb - fa >= 0;
  fb - fa
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
  result := CountDivisiblesInRange_aux(k, a, b);
}
// </vc-code>

