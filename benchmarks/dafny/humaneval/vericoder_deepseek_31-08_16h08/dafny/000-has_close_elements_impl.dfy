function abs(val : real): real
{
  if (val < 0.0) then
    -val
  else
    val
}

// <vc-helpers>
lemma {:induction false} CloseElementsLemma(numbers: seq<real>, threshold: real) 
  requires threshold > 0.0
  ensures (exists i: int, j: int :: i >= 0 && j >= 0 && i < |numbers| && j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold) ==
          (exists i: int :: 0 <= i < |numbers| && 
             exists j: int :: 0 <= j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold)
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
  var i := 0;
  while (i < |numbers|)
    invariant 0 <= i <= |numbers|
    invariant i > 0 ==> !(exists k: int, l: int :: 0 <= k < i && 0 <= l < i && k != l && abs(numbers[k] - numbers[l]) < threshold)
  {
    var j := 0;
    while (j < i)
      invariant 0 <= j <= i
      invariant forall l: int :: 0 <= l < j ==> abs(numbers[i] - numbers[l]) >= threshold
    {
      if (abs(numbers[i] - numbers[j]) < threshold) {
        flag := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  flag := false;
}
// </vc-code>

