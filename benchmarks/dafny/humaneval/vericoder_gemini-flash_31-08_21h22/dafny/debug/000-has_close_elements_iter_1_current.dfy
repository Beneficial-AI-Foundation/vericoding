function abs(val : real): real
{
  if (val < 0.0) then
    -val
  else
    val
}

// <vc-helpers>
lemma lemma_abs_diff_symm(a: real, b: real)
  ensures abs(a - b) == abs(b - a)
{
  // No body needed for this lemma, abs definition handles it
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
  var n := |numbers>;
  if n < 2 {
    return false;
  }

  var i := 0;
  while i < n {
    var j := i + 1;
    while j < n {
      if abs(numbers[i] - numbers[j]) < threshold {
        return true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

