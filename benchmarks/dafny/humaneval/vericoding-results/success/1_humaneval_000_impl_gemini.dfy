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

// </vc-helpers>

// <vc-spec>
method has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
    requires ValidInput(numbers, threshold)
    ensures result == HasCloseElements(numbers, threshold)
// </vc-spec>
// <vc-code>
{
  result := false;
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant !result ==> forall k, l :: 0 <= k < i && k < l < |numbers| ==> AbsDiff(numbers[k], numbers[l]) >= threshold
  {
    var j := i + 1;
    while j < |numbers|
      invariant 0 <= i < |numbers|
      invariant i + 1 <= j <= |numbers|
      invariant !result ==> forall k :: i + 1 <= k < j ==> AbsDiff(numbers[i], numbers[k]) >= threshold
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
