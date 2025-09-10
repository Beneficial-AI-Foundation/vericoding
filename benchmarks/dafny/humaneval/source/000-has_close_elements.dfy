function abs(val : real): real
{
  if (val < 0.0) then
    -val
  else
    val
}
// pure-end
method has_close_elements(numbers: seq<real>, threshold: real) returns (flag : bool)
  // pre-conditions-start
  requires threshold > 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures flag == (exists i: int, j: int :: i >= 0 && j >= 0 && i < |numbers| && j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold)
  // post-conditions-end
{
  // impl-start
  flag := false;
  for i := 0 to |numbers|
    // invariants-start
    invariant flag == (exists i1: int, j1: int :: i1 >= 0 && j1 >= 0 && i1 < i && j1 < |numbers| && i1 != j1 && abs(numbers[i1] - numbers[j1]) < threshold)
    // invariants-end
  {
    for j := 0 to |numbers|
      // invariants-start
      invariant flag == (exists i1: int, j1: int :: i1 >= 0 && j1 >= 0 && ((i1 < i && j1 < |numbers|) || (i1 == i && j1 < j)) && i1 != j1 && abs(numbers[i1] - numbers[j1]) < threshold)
      // invariants-end
    {
      if (i != j)
      {
        var distance: real := abs(numbers[i] - numbers[j]);
        if (distance < threshold)
        {
          flag := true;
        }
      }
    }
  }
  // impl-end
}
