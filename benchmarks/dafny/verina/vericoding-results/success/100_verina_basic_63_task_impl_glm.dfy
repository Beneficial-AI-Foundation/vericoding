// <vc-preamble>
function AbsDiff(a: int, b: int): int
{
    if a >= b then a - b else b - a
}
// </vc-preamble>

// <vc-helpers>
lemma AbsDiffSymmetric(a: int, b: int)
  ensures AbsDiff(a, b) == AbsDiff(b, a)
{
  if a >= b {
    assert AbsDiff(a, b) == a - b;
    assert AbsDiff(b, a) == a - b;
  } else {
    assert AbsDiff(a, b) == b - a;
    assert AbsDiff(b, a) == b - a;
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
  /* code modified by LLM (iteration 2): fixed inner loop invariant to avoid index out of range */
  var i := 0;
  while i < numbers.Length
      invariant 
        forall i0 :: 0 <= i0 < i ==> 
            forall j0 :: i0+1 <= j0 < numbers.Length ==> AbsDiff(numbers[i0], numbers[j0]) >= threshold
  {
      var j := i + 1;
      while j < numbers.Length
          invariant 
            forall j0 :: i+1 <= j0 < j && j0 < numbers.Length ==> AbsDiff(numbers[i], numbers[j0]) >= threshold
      {
          if AbsDiff(numbers[i], numbers[j]) < threshold {
              return true;
          }
          j := j + 1;
      }
      i := i + 1;
  }
  return false;
}
// </vc-code>
