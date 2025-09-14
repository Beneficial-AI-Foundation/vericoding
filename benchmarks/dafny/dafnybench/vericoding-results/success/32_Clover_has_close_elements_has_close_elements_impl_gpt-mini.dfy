

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method has_close_elements(numbers: seq<real>, threshold: real) returns (res: bool)
  requires threshold >= 0.0
  ensures res ==> exists i: int, j: int :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) < threshold
  ensures !res ==> (forall i: int, j: int :: 1 <= i < |numbers| && 0 <= j < i ==>  (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) >= threshold)
// </vc-spec>
// <vc-code>
{
  if |numbers| <= 1 {
    return false;
  }
  var n := |numbers|;
  var i := 1;
  while i < n
    invariant 1 <= i && i <= n
    invariant forall a,b :: 1 <= a < i && 0 <= b < a ==>
      (if numbers[a] - numbers[b] < 0.0 then numbers[b] - numbers[a] else numbers[a] - numbers[b]) >= threshold
  {
    var j := 0;
    while j < i
      invariant 0 <= j && j <= i
      invariant forall a,b :: 1 <= a < i && 0 <= b < a ==>
        (if numbers[a] - numbers[b] < 0.0 then numbers[b] - numbers[a] else numbers[a] - numbers[b]) >= threshold
      invariant forall k :: 0 <= k < j ==>
        (if numbers[i] - numbers[k] < 0.0 then numbers[k] - numbers[i] else numbers[i] - numbers[k]) >= threshold
    {
      var diff := if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j];
      if diff < threshold {
        assert exists i0,j0 ::
          i0 == i && j0 == j &&
          0 <= i0 < n && 0 <= j0 < n && i0 != j0 &&
          (if numbers[i0] - numbers[j0] < 0.0 then numbers[j0] - numbers[i0] else numbers[i0] - numbers[j0]) < threshold;
        return true;
      }
      j := j + 1;
    }
    assert forall a,b :: 1 <= a < i+1 && 0 <= b < a ==>
      (if numbers[a] - numbers[b] < 0.0 then numbers[b] - numbers[a] else numbers[a] - numbers[b]) >= threshold;
    i := i + 1;
  }
  return false;
}
// </vc-code>

