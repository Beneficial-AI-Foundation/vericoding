function abs(x: real): real
{
  if x < 0.0 then -x else x
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
    ensures result <==> exists i, j ::
      0 <= i < |numbers| &&
      0 <= j < |numbers| &&
      i != j &&
      abs(numbers[i] - numbers[j]) < threshold
    ensures result ==> |numbers| > 1
// </vc-spec>
// <vc-code>
{
  var n := |numbers|;
  if n <= 1 {
    return false;
  }

  var i := 0;
  while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant forall a, b :: 0 <= a < i && 0 <= b < n && a != b ==> abs(numbers[a] - numbers[b]) >= threshold
  {
    var j := i + 1;
    while j < n
      decreases n - j
      invariant 0 <= j <= n
      invariant forall a, b :: 0 <= a < i && 0 <= b < n && a != b ==> abs(numbers[a] - numbers[b]) >= threshold
      invariant forall b :: i < b < j ==> abs(numbers[i] - numbers[b]) >= threshold
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

