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
  flag := false;
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant flag == (exists i': int, j': int :: 0 <= i' < i && 0 <= j' < |numbers| && i' != j' && abs(numbers[i'] - numbers[j']) < threshold)
  {
    var j := 0;
    while j < |numbers|
      invariant 0 <= j <= |numbers|
      invariant flag == (exists i': int, j': int :: (0 <= i' < i && 0 <= j' < |numbers| && i' != j' && abs(numbers[i'] - numbers[j']) < threshold) || 
                                                      (i' == i && 0 <= j' < j && i' != j' && abs(numbers[i'] - numbers[j']) < threshold))
    {
      if i != j && abs(numbers[i] - numbers[j]) < threshold {
        flag := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

