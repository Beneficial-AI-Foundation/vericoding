function abs(val : real): real
{
  if (val < 0.0) then
    -val
  else
    val
}

// <vc-helpers>
// Helper predicate to check if two real numbers are within a threshold
predicate CloseEnough(a: real, b: real, threshold: real)
{
  abs(a - b) <= threshold
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
  ensures result == exists i, j :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && CloseEnough(numbers[i], numbers[j], threshold)
// </vc-spec>
// <vc-code>
{
  if |numbers| < 2 {
    return false;
  }

  for i := 0 to |numbers|
    invariant 0 <= i <= |numbers|
    invariant forall k, l :: 0 <= k < i && 0 <= l < |numbers| && k != l ==> !CloseEnough(numbers[k], numbers[l], threshold)
  {
    for j := i + 1 to |numbers|
      invariant 0 <= i < j <= |numbers|
      invariant forall k, l :: 0 <= k < i && 0 <= l < |numbers| && k != l ==> !CloseEnough(numbers[k], numbers[l], threshold)
      invariant forall l :: i < l < j ==> !CloseEnough(numbers[i], numbers[l], threshold)
    {
      if CloseEnough(numbers[i], numbers[j], threshold) {
        return true;
      }
    }
  }
  return false;
}
// </vc-code>
