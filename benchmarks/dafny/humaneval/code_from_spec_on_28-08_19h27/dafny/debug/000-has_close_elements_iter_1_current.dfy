function abs(val : real): real
{
  if (val < 0.0) then
    -val
  else
    val
}

// <vc-helpers>
predicate hasCloseElements(numbers: seq<real>, threshold: real)
{
  exists i, j :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def has_close_elements(numbers: List[float], threshold: float) -> bool
*/
// </vc-description>

// <vc-spec>
method HasCloseElements(numbers: seq<real>, threshold: real) returns (result: bool)
  requires threshold >= 0.0
  ensures result == hasCloseElements(numbers, threshold)
// </vc-spec>
// <vc-code>
{
  result := false;
  var i := 0;
  while i < |numbers| && !result
    invariant 0 <= i <= |numbers|
    invariant result == exists i', j' :: 0 <= i' < i && 0 <= j' < |numbers| && i' != j' && abs(numbers[i'] - numbers[j']) < threshold
  {
    var j := 0;
    while j < |numbers| && !result
      invariant 0 <= j <= |numbers|
      invariant result == (exists i', j' :: (0 <= i' < i && 0 <= j' < |numbers| && i' != j' && abs(numbers[i'] - numbers[j']) < threshold) ||
                                       (i' == i && 0 <= j' < j && i' != j' && abs(numbers[i'] - numbers[j']) < threshold))
    {
      if i != j && abs(numbers[i] - numbers[j]) < threshold {
        result := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
