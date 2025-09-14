

// <vc-helpers>
lemma abs_diff_properties(a: real, b: real)
  ensures (if a - b < 0.0 then b - a else a - b) >= 0.0
{
}

lemma abs_diff_symmetric(a: real, b: real)
  ensures (if a - b < 0.0 then b - a else a - b) == (if b - a < 0.0 then a - b else b - a)
{
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
  if |numbers| <= 1 {
    return false;
  }
  
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant forall k: int, l: int :: 1 <= k < i && 0 <= l < k ==> (if numbers[k] - numbers[l] < 0.0 then numbers[l] - numbers[k] else numbers[k] - numbers[l]) >= threshold
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant forall k: int, l: int :: 1 <= k < i && 0 <= l < k ==> (if numbers[k] - numbers[l] < 0.0 then numbers[l] - numbers[k] else numbers[k] - numbers[l]) >= threshold
      invariant forall l: int :: 0 <= l < j ==> (if numbers[i] - numbers[l] < 0.0 then numbers[l] - numbers[i] else numbers[i] - numbers[l]) >= threshold
    {
      var diff := if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j];
      if diff < threshold {
        return true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

