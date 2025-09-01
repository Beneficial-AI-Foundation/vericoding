function abs(val : real): real
{
  if (val < 0.0) then
    -val
  else
    val
}

// <vc-helpers>
// </vc-helpers>
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
  var flag := false;
  var idx1 := 0;
  while idx1 < |numbers|
    invariant 0 <= idx1 <= |numbers|
    invariant flag ==> exists i, j :: 0 <= i < idx1 && 0 <= j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold
    decreases |numbers| - idx1
  {
    var idx2 := 0;
    while idx2 < |numbers|
      invariant 0 <= idx2 <= |numbers|
      invariant flag ==> (exists i, j :: 0 <= i < idx1 && 0 <= j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold) || (exists j :: 0 <= j < idx2 && idx1 != j && abs(numbers[idx1] - numbers[j]) < threshold)
      decreases |numbers| - idx2
    {
      if idx2 != idx1 && abs(numbers[idx1] - numbers[idx2]) < threshold {
        flag := true;
      }
      idx2 := idx2 + 1;
    }
    idx1 := idx1 + 1;
  }
}
// </vc-code>

