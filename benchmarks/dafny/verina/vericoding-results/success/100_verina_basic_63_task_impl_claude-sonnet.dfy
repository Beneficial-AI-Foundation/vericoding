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
    invariant !result <==> (forall x: int, y: int :: 
      0 <= x < i && 0 <= y < numbers.Length && x != y ==> 
      AbsDiff(numbers[x], numbers[y]) >= threshold)
  {
    var j := 0;
    while j < numbers.Length
      invariant 0 <= j <= numbers.Length
      invariant !result <==> (forall x: int, y: int :: 
        (0 <= x < i && 0 <= y < numbers.Length && x != y) || 
        (x == i && 0 <= y < j && x != y) ==> 
        AbsDiff(numbers[x], numbers[y]) >= threshold)
    {
      if i != j && AbsDiff(numbers[i], numbers[j]) < threshold {
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
