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
  result := false;
  var i := 0;
  while i < numbers.Length
    invariant 0 <= i <= numbers.Length
    invariant forall k, l :: 0 <= k < i && k < l < numbers.Length ==> AbsDiff(numbers[k], numbers[l]) >= threshold
  {
    var j := i + 1;
    while j < numbers.Length
      invariant i < numbers.Length
      invariant i + 1 <= j <= numbers.Length
      invariant forall k, l :: 0 <= k < i && k < l < numbers.Length ==> AbsDiff(numbers[k], numbers[l]) >= threshold
      invariant forall l :: i < l < j ==> AbsDiff(numbers[i], numbers[l]) >= threshold
    {
      if AbsDiff(numbers[i], numbers[j]) < threshold {
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
