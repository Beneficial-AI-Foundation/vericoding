function abs(val : real): real
{
  if (val < 0.0) then
    -val
  else
    val
}

// <vc-helpers>
lemma AbsDifferenceProperty(a: real, b: real)
  ensures abs(a - b) == abs(b - a)
{
  if (a - b < 0.0) {
    assert a - b == -(b - a);
    assert abs(a - b) == -(a - b) == b - a;
    assert abs(b - a) == b - a;
  } else {
    assert abs(a - b) == a - b;
    assert abs(b - a) == a - b;
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
  if |numbers| < 2 {
    return false;
  }
  
  var i := 0;
  while i < |numbers| 
    invariant 0 <= i <= |numbers|
    invariant forall k, l :: 0 <= k < i && k < l < |numbers| ==> abs(numbers[k] - numbers[l]) >= threshold
  {
    var j := i + 1;
    while j < |numbers| 
      invariant 0 <= i < |numbers|
      invariant i < j <= |numbers|
      invariant forall l :: i < l < j ==> abs(numbers[i] - numbers[l]) >= threshold
    {
      var diff := numbers[i] - numbers[j];
      if abs(diff) < threshold {
        return true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>
