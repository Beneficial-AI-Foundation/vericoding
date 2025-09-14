function abs(val : real): real
{
  if (val < 0.0) then
    -val
  else
    val
}

// <vc-helpers>
// (no helper code needed)
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
  var n := |numbers|;
  var i := 0;
  while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant forall p,q :: 0 <= p < i && 0 <= q < n && p != q ==> !(abs(numbers[p] - numbers[q]) < threshold)
  {
    var j := i + 1;
    while j < n
      decreases n - j
      invariant 0 <= j <= n
      invariant 0 <= i <= n
      invariant forall p,q :: 0 <= p < i && 0 <= q < n && p != q ==> !(abs(numbers[p] - numbers[q]) < threshold)
      invariant forall q2 :: i + 1 <= q2 < j ==> !(abs(numbers[i] - numbers[q2]) < threshold)
    {
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

