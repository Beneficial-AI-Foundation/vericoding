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
{
  /* code modified by LLM (iteration 3): [Corrected loop invariants to match the algorithm's logic] */
  flag := false;
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant !flag ==> forall k, l :: 0 <= k < i && k < l < |numbers| ==> abs(numbers[k] - numbers[l]) >= threshold
  {
    var j := i + 1;
    while j < |numbers|
      invariant 0 <= i <= |numbers|
      invariant i < j <= |numbers|
      invariant !flag ==> forall k, l :: 0 <= k < i && k < l < |numbers| ==> abs(numbers[k] - numbers[l]) >= threshold
      invariant !flag ==> forall l :: i < l < j ==> abs(numbers[i] - numbers[l]) >= threshold
    {
      if abs(numbers[i] - numbers[j]) < threshold {
        flag := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
