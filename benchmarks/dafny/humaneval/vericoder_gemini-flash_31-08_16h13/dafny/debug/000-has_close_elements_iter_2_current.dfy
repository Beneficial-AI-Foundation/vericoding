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
  if a - b < 0.0 {
    calc {
      abs(a - b);
      -(a - b);
      b - a;
      abs(b - a);
    }
  } else {
    calc {
      abs(a - b);
      a - b;
      -(b - a);
      abs(b - a);
    }
  }
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
  var n := |numbers|;
  var found := false;

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant found ==> (exists k: int, l: int :: 0 <= k < i && k < l && l < n && abs(numbers[k] - numbers[l]) < threshold)
    invariant !found ==> (forall k: int, l: int :: 0 <= k < i && k < l && l < n ==> abs(numbers[k] - numbers[l]) >= threshold)
  {
    var j := i + 1;
    while j < n
      invariant i < j <= n
      invariant found ==> (exists k: int, l: int :: (0 <= k < i && k < l && l < n && abs(numbers[k] - numbers[l]) < threshold) || (k == i && i < l && l < j && abs(numbers[k] - numbers[l]) < threshold))
      invariant !found ==> (forall k: int, l: int :: (0 <= k < i && k < l && l < n ==> abs(numbers[k] - numbers[l]) >= threshold) && (k == i && i < l && l < j ==> abs(numbers[k] - numbers[l]) >= threshold))
    {
      if abs(numbers[i] - numbers[j]) < threshold {
        found := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  flag := found;
}
// </vc-code>

