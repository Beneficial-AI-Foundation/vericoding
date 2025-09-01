function abs(val : real): real
{
  if (val < 0.0) then
    -val
  else
    val
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method has_close_elements(numbers: seq<real>, threshold: real) returns (flag : bool)
  // pre-conditions-start
  requires threshold > 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures flag == (exists i: int, j: int :: i >= 0 && j >= 0 && i < |numbers| && j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |numbers| < 2 {
    return false;
  }
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant forall k: int, l: int :: 0 <= k < i && k < l < |numbers| ==> abs(numbers[k] - numbers[l]) >= threshold
  {
    var j := i + 1;
    while j < |numbers|
      invariant i < j <= |numbers|
      invariant forall l: int :: i+1 <= l < j ==> abs(numbers[i] - numbers[l]) >= threshold
    {
      if abs(numbers[i] - numbers[j]) < threshold {
        return true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

