

// <vc-helpers>
function abs_diff(x: real, y: real): real {
  if x < y then y - x else x - y
}

lemma abs_diff_properties(x: real, y: real)
  ensures abs_diff(x, y) >= 0.0
  ensures abs_diff(x, y) == abs_diff(y, x)
  ensures (x <= y) ==> abs_diff(x, y) == y - x
  ensures (y <= x) ==> abs_diff(x, y) == x - y
{
  if x < y {
    assert abs_diff(x, y) == y - x;
  } else {
    assert abs_diff(x, y) == x - y;
  }

  if x < y {
    assert y - x >= 0.0;
  } else {
    assert x - y >= 0.0;
  }

  if x < y {
    assert abs_diff(x, y) == y - x;
    assert abs_diff(y, x) == y - x;
  } else if y < x {
    assert abs_diff(x, y) == x - y;
    assert abs_diff(y, x) == x - y;
  } else {
    assert x == y;
    assert abs_diff(x, y) == 0.0;
    assert abs_diff(y, x) == 0.0;
  }

  if x <= y {
    if x < y {
      assert abs_diff(x, y) == y - x;
    } else {
      assert x == y;
      assert abs_diff(x, y) == 0.0;
      assert y - x == 0.0;
    }
  }

  if y <= x {
    if y < x {
      assert abs_diff(x, y) == x - y;
    } else {
      assert y == x;
      assert abs_diff(x, y) == 0.0;
      assert x - y == 0.0;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method has_close_elements(numbers: seq<real>, threshold: real) returns (res: bool)
  requires threshold >= 0.0
  ensures res ==> exists i: int, j: int :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) < threshold
  ensures !res ==> (forall i: int, j: int :: 1 <= i < |numbers| && 0 <= j < i ==>  (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) >= threshold)
// </vc-spec>
// <vc-code>
{
  if |numbers| < 2 {
    return false;
  }
  
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant forall k: int, l: int :: 0 <= k < l < i ==> abs_diff(numbers[k], numbers[l]) >= threshold
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant forall l: int :: 0 <= l < j ==> abs_diff(numbers[i], numbers[l]) >= threshold
    {
      if abs_diff(numbers[i], numbers[j]) < threshold {
        return true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

