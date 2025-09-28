// <vc-preamble>
function AbsDiff(a: int, b: int): int
{
    if a >= b then a - b else b - a
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HasCloseElements(numbers: array<int>, threshold: int) returns (result: bool)
    requires threshold >= 0
    ensures
        !result <==> (forall i: int, j: int :: 
            0 <= i < numbers.Length && 0 <= j < numbers.Length && i != j ==> 
            AbsDiff(numbers[i], numbers[j]) >= threshold)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed loop invariants and added decreases clauses to verify the method correctly */
  var i := 0;
  while i < numbers.Length 
    invariant 0 <= i <= numbers.Length
    invariant forall x, y :: 0 <= x < i && 0 <= y < i && x != y ==> AbsDiff(numbers[x], numbers[y]) >= threshold
    decreases numbers.Length - i
  {
    var j := 0;
    while j < numbers.Length
      invariant 0 <= j <= numbers.Length
      invariant forall y :: 0 <= y < j && y != i ==> AbsDiff(numbers[i], numbers[y]) >= threshold
      decreases numbers.Length - j
    {
      if i != j {
        if AbsDiff(numbers[i], numbers[j]) < threshold {
          result := true;
          return;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := false;
}
// </vc-code>
