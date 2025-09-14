// <vc-preamble>
function AbsDiff(a: int, b: int): int
{
    if a >= b then a - b else b - a
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed predicate to use distinct indices */
predicate HasCloseElementsAt(numbers: array<int>, threshold: int, i: int, j: int)
  reads numbers
{
  0 <= i < numbers.Length && 0 <= j < numbers.Length && i != j && AbsDiff(numbers[i], numbers[j]) < threshold
}

lemma CloseElementsEquivalence(numbers: array<int>, threshold: int)
  ensures (exists i: int, j: int :: HasCloseElementsAt(numbers, threshold, i, j)) <==> !(forall i: int, j: int :: 0 <= i < numbers.Length && 0 <= j < numbers.Length && i != j ==> AbsDiff(numbers[i], numbers[j]) >= threshold)
{
  if (exists i: int, j: int :: HasCloseElementsAt(numbers, threshold, i, j)) {
    var i, j :| HasCloseElementsAt(numbers, threshold, i, j);
    assert !(forall x: int, y: int :: 0 <= x < numbers.Length && 0 <= y < numbers.Length && x != y ==> AbsDiff(numbers[x], numbers[y]) >= threshold);
  }
  if !(forall i: int, j: int :: 0 <= i < numbers.Length && 0 <= j < numbers.Length && i != j ==> AbsDiff(numbers[i], numbers[j]) >= threshold) {
    assert exists i: int, j: int :: 0 <= i < numbers.Length && 0 <= j < numbers.Length && i != j && AbsDiff(numbers[i], numbers[j]) < threshold;
    var i, j :| 0 <= i < numbers.Length && 0 <= j < numbers.Length && i != j && AbsDiff(numbers[i], numbers[j]) < threshold;
    assert HasCloseElementsAt(numbers, threshold, i, j);
  }
}
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
  /* code modified by LLM (iteration 3): simplified implementation without helper usage */
  var i := 0;
  while i < numbers.Length
    invariant 0 <= i <= numbers.Length
    invariant forall x: int, y: int :: 0 <= x < i && 0 <= y < numbers.Length && x != y ==> AbsDiff(numbers[x], numbers[y]) >= threshold
    invariant forall x: int, y: int :: 0 <= x < numbers.Length && 0 <= y < i && x != y ==> AbsDiff(numbers[x], numbers[y]) >= threshold
  {
    var j := 0;
    while j < numbers.Length
      invariant 0 <= j <= numbers.Length
      invariant forall x: int, y: int :: 0 <= x < i && 0 <= y < numbers.Length && x != y ==> AbsDiff(numbers[x], numbers[y]) >= threshold
      invariant forall x: int, y: int :: 0 <= x < numbers.Length && 0 <= y < i && x != y ==> AbsDiff(numbers[x], numbers[y]) >= threshold
      invariant forall y: int :: 0 <= y < j && i != y ==> AbsDiff(numbers[i], numbers[y]) >= threshold
    {
      if i != j && AbsDiff(numbers[i], numbers[j]) < threshold {
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := false;
}
// </vc-code>
