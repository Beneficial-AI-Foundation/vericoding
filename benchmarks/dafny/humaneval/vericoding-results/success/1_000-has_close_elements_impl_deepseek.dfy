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
/* helper modified by LLM (iteration 5): Remove duplicate abs function and simplify helpers */
lemma ExistenceEquivalenceLemma(numbers: seq<real>, threshold: real)
  requires threshold > 0.0
  ensures (exists i: int, j: int :: i >= 0 && j >= 0 && i < |numbers| && j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold) == (exists i: int, j: int :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold)
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
  /* code modified by LLM (iteration 5): Simplified implementation with nested loops */
  flag := false;
  var i: int := 0;
  
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant !flag ==> forall k: int, l: int :: 0 <= k < i && 0 <= l < |numbers| && k != l ==> abs(numbers[k] - numbers[l]) >= threshold
    invariant flag ==> exists k: int, l: int :: 0 <= k < i && 0 <= l < |numbers| && k != l && abs(numbers[k] - numbers[l]) < threshold
    decreases |numbers| - i
  {
    var j: int := i + 1;
    while j < |numbers|
      invariant i < j <= |numbers|
      invariant !flag ==> forall l: int :: i < l < j ==> abs(numbers[i] - numbers[l]) >= threshold
      invariant flag ==> exists l: int :: i < l < j && abs(numbers[i] - numbers[l]) < threshold
      decreases |numbers| - j
    {
      if abs(numbers[i] - numbers[j]) < threshold {
        flag := true;
        break;
      }
      j := j + 1;
    }
    if flag {
      break;
    }
    i := i + 1;
  }
}
// </vc-code>
