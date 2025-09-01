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
  for i := 0 to |numbers| - 2 {
    invariant for all a, b : int :: 0 <= a < i && a < b < |numbers| ==> abs(numbers[a] - numbers[b]) >= threshold;
    variant |numbers| - i;
    for j := i + 1 to |numbers| - 1 {
      invariant for all b : int :: i < b < j ==> abs(numbers[i] - numbers[b]) >= threshold;
      variant |numbers| - j;
      if abs(numbers[i] - numbers[j]) < threshold {
        return true;
      }
    }
  }
  return false;
}
// </vc-code>

