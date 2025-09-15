// <vc-preamble>
function abs(val : real): real
{
  if (val < 0.0) then
    -val
  else
    val
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method has_close_elements(numbers: seq<real>, threshold: real) returns (flag : bool)

  requires threshold > 0.0

  ensures flag == (exists i: int, j: int :: i >= 0 && j >= 0 && i < |numbers| && j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Initialize 'flag' to `false` before loops. */
{
  flag := false;
  var i: int := 0;
  while i < |numbers|
    decreases |numbers| - i
    invariant 0 <= i <= |numbers|
    invariant flag == (exists k: int, l: int :: 0 <= k < i && 0 <= l < |numbers| && k != l && abs(numbers[k] - numbers[l]) < threshold)
  {
    var j: int := 0;
    while j < |numbers|
      decreases |numbers| - j
      invariant 0 <= j <= |numbers|
      invariant flag == ((exists k: int, l: int :: (0 <= k < i && 0 <= l < |numbers| && k != l && abs(numbers[k] - numbers[l]) < threshold)) || (exists k: int, l: int :: (k == i && 0 <= l < j && k != l && abs(numbers[k] - numbers[l]) < threshold)))
    {
      if i != j && abs(numbers[i] - numbers[j]) < threshold {
        flag := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  // flag is already false; no need to assign again
}
// </vc-code>
