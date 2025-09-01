function abs(val : real): real
{
  if (val < 0.0) then
    -val
  else
    val
}

// <vc-helpers>
// Empty
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
  flag := false;
  var idx := 0;
  while idx < |numbers|
    invariant 0 <= idx <= |numbers|
    invariant flag == (exists i: int, j: int :: 0 <= i < idx && i < j < |numbers| && abs(numbers[i] - numbers[j]) < threshold)
    decreases |numbers| - idx
  {
    var idx2 := idx + 1;
    while idx2 < |numbers|
      invariant idx + 1 <= idx2 <= |numbers|
      invariant flag == (exists i: int, j: int :: 0 <= i < idx && i < j < |numbers| && abs(numbers[i] - numbers[j]) < threshold) || (exists j: int :: idx < j < idx2 && abs(numbers[idx] - numbers[j]) < threshold)
      decreases |numbers| - idx2
    {
      if abs(numbers[idx] - numbers[idx2]) < threshold {
        flag := true;
      }
      idx2 := idx2 + 1;
    }
    idx := idx + 1;
  }
}
// </vc-code>

