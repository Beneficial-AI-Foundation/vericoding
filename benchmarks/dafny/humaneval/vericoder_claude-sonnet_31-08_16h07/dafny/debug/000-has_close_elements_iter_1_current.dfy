function abs(val : real): real
{
  if (val < 0.0) then
    -val
  else
    val
}

// <vc-helpers>
lemma abs_properties(x: real, y: real)
  ensures abs(x - y) == abs(y - x)
{
}

lemma abs_non_negative(x: real)
  ensures abs(x) >= 0.0
{
}
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
    invariant flag == (exists i1: int, j1: int :: i1 >= 0 && j1 >= 0 && i1 < i && j1 < |numbers| && i1 != j1 && abs(numbers[i1] - numbers[j1]) < threshold)
  {
    var j := 0;
    while j < |numbers|
      invariant 0 <= j <= |numbers|
      invariant flag == (exists i1: int, j1: int :: 
        (i1 >= 0 && j1 >= 0 && i1 < i && j1 < |numbers| && i1 != j1 && abs(numbers[i1] - numbers[j1]) < threshold) ||
        (i1 == i && j1 >= 0 && j1 < j && i1 != j1 && abs(numbers[i1] - numbers[j1]) < threshold))
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

