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
function has_close_pair(numbers: seq<real>, threshold: real, max_idx: int): bool
  requires threshold > 0.0
  requires 0 <= max_idx <= |numbers|
{
  exists i: int, j: int :: i >= 0 && j >= 0 && i < max_idx && j < max_idx && i != j && abs(numbers[i] - numbers[j]) < threshold
}

lemma close_elements_monotonic(numbers: seq<real>, threshold: real, k: int)
  requires threshold > 0.0
  requires 0 <= k <= |numbers|
  requires has_close_pair(numbers, threshold, k)
  ensures has_close_pair(numbers, threshold, |numbers|)
{
}
// </vc-helpers>

// <vc-spec>
method has_close_elements(numbers: seq<real>, threshold: real) returns (flag : bool)

  requires threshold > 0.0

  ensures flag == (exists i: int, j: int :: i >= 0 && j >= 0 && i < |numbers| && j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold)
// </vc-spec>
// <vc-code>
{
  flag := false;
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant flag == has_close_pair(numbers, threshold, i)
  {
    var j := 0;
    while j < |numbers|
      invariant 0 <= j <= |numbers|
      invariant flag == (has_close_pair(numbers, threshold, i) || (exists k: int :: k >= 0 && k < j && k != i && abs(numbers[i] - numbers[k]) < threshold))
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
