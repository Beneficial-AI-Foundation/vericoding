// <vc-preamble>

predicate ValidInput(numbers: seq<real>, threshold: real)
{
    true
}

function AbsDiff(a: real, b: real): real
{
    if a >= b then a - b else b - a
}

predicate HasCloseElements(numbers: seq<real>, threshold: real)
{
    exists i, j :: 0 <= i < j < |numbers| && AbsDiff(numbers[i], numbers[j]) < threshold
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): predicate to describe a close pair */
predicate PairClose(numbers: seq<real>, i: int, j: int, threshold: real)
{
  0 <= i < j < |numbers| && AbsDiff(numbers[i], numbers[j]) < threshold
}
// </vc-helpers>

// <vc-spec>
method has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
    requires ValidInput(numbers, threshold)
    ensures result == HasCloseElements(numbers, threshold)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): nested loops to find close elements without warnings */
  var n := |numbers|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall p,q :: 0 <= p < i && p < q < n ==> AbsDiff(numbers[p], numbers[q]) >= threshold
  {
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant forall p,q :: 0 <= p < i && p < q < n ==> AbsDiff(numbers[p], numbers[q]) >= threshold
      invariant forall q :: i < q < j ==> AbsDiff(numbers[i], numbers[q]) >= threshold
    {
      if AbsDiff(numbers[i], numbers[j]) < threshold {
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
