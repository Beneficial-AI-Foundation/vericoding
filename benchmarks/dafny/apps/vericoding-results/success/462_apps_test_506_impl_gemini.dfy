predicate ValidInput(a: int, b: int)
{
    a > 0 && b > 0
}

function countSquares(a: int, b: int): int
    requires a >= 0 && b >= 0
    ensures a > 0 && b > 0 && a > b ==> countSquares(a, b) >= 1
    ensures a > 0 && b > 0 && b > a ==> countSquares(a, b) >= 1
    ensures a > 0 && b > 0 && a == b ==> countSquares(a, b) == 1
    decreases a + b
{
    if a == 0 || b == 0 then 0
    else if a > b then a / b + countSquares(a % b, b)
    else b / a + countSquares(a, b % a)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
    requires ValidInput(a, b)
    ensures result >= 0
    ensures (a == b) ==> (result == 1)
    ensures a > b ==> result >= 1
    ensures result == countSquares(a, b)
// </vc-spec>
// <vc-code>
{
  var current_a := a;
  var current_b := b;
  result := 0;

  while current_a > 0 && current_b > 0
    invariant current_a >= 0 && current_b >= 0
    invariant result + countSquares(current_a, current_b) == countSquares(a, b)
    decreases current_a + current_b
  {
    if current_a > current_b {
      result := result + current_a / current_b;
      current_a := current_a % current_b;
    } else {
      result := result + current_b / current_a;
      current_b := current_b % current_a;
    }
  }
}
// </vc-code>

