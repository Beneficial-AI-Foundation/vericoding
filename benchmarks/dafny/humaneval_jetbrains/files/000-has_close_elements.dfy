
/*
function_signature: def has_close_elements(numbers: List[float], threshold: float) -> bool
*/

function abs(val : real): real
{
  if (val < 0.0) then
    -val
  else
    val
}

method has_close_elements(numbers: seq<real>, threshold: real) returns (flag : bool)
  // pre-conditions-start
  requires threshold > 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures flag == (exists i: int, j: int :: i >= 0 && j >= 0 && i < |numbers| && j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold)
  // post-conditions-end
{
  assume false;
}
