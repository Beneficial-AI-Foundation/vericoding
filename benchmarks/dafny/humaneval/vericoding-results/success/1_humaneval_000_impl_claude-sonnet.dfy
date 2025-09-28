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
/* helper modified by LLM (iteration 5): fixed predicate to track all pairs found up to current position */
predicate HasCloseElementsUpTo(numbers: seq<real>, threshold: real, bound: int)
  requires 0 <= bound <= |numbers|
{
  exists i, j :: 0 <= i < j < |numbers| && i < bound && AbsDiff(numbers[i], numbers[j]) < threshold
}

predicate HasCloseElementsPartial(numbers: seq<real>, threshold: real, outerBound: int, innerBound: int)
  requires 0 <= outerBound <= |numbers|
  requires outerBound <= innerBound <= |numbers|
{
  exists i, j :: 0 <= i < j < |numbers| && ((i < outerBound) || (i == outerBound && outerBound + 1 <= j < innerBound)) && AbsDiff(numbers[i], numbers[j]) < threshold
}
// </vc-helpers>

// <vc-spec>
method has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
    requires ValidInput(numbers, threshold)
    ensures result == HasCloseElements(numbers, threshold)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed invariants with helper predicate for partial progress */
  result := false;
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant result ==> HasCloseElementsUpTo(numbers, threshold, i)
    invariant !result ==> !HasCloseElementsUpTo(numbers, threshold, i)
  {
    var j := i + 1;
    while j < |numbers|
      invariant i + 1 <= j <= |numbers|
      invariant result ==> HasCloseElementsPartial(numbers, threshold, i, j)
      invariant !result ==> !HasCloseElementsPartial(numbers, threshold, i, j)
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
