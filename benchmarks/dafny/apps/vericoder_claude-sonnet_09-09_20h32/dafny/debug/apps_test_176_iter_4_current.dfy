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
    assert (a / b) * b <= a < (a / b + 1) * b;
  } else {
    assert FloorDiv(a, b) == (a - b + 1) / b;
    var q := (a - b + 1) / b;
    assert q * b <= a - b + 1 < (q + 1) * b;
    
    calc {
      q * b;
      <= a - b + 1;
      < a - b + 1 + b;
      == a + 1;
    }
    
    calc {
      a - b + 1;
      < (q + 1) * b;
      a < (q + 1) * b + b - 1;
      a < (q + 1) * b;
    }
  }
}

lemma CountDivisiblesNonNegative(k: int, a: int, b: int)
  requires k > 0
  requires a <= b
  ensures CountDivisiblesInRange(k, a, b) >= 0
{
  FloorDivProperties(b, k);
  FloorDivProperties(a - 1, k);
  
  var floorB := FloorDiv(b, k);
  var floorA := FloorDiv(a - 1, k);
  
  assert floorB * k <= b;
  assert floorA * k <= a - 1;
  assert a - 1 < b;
  assert floorA * k < floorB * k + k;
  assert floorA < floorB + 1;
  assert floorA <= floorB;
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
  FloorDivProperties(a - 1, k);
  var floorB := FloorDiv(b, k);
  var floorA := FloorDiv(a - 1, k);
  result := floorB - floorA;
  
  CountDivisiblesNonNegative(k, a, b);
}
// </vc-code>

