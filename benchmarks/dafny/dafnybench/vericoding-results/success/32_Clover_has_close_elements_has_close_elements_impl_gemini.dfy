// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function abs_real(r: real): real { if r < 0.0 then -r else r }
// </vc-helpers>

// <vc-spec>
method has_close_elements(numbers: seq<real>, threshold: real) returns (res: bool)
  requires threshold >= 0.0
  ensures res ==> exists i: int, j: int :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) < threshold
  ensures !res ==> (forall i: int, j: int :: 1 <= i < |numbers| && 0 <= j < i ==>  (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) >= threshold)
// </vc-spec>
// <vc-code>
{
  res := false;
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant !res ==> forall k, l :: 0 <= l < k < i ==> abs_real(numbers[k] - numbers[l]) >= threshold
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant !res ==> forall l :: 0 <= l < j ==> abs_real(numbers[i] - numbers[l]) >= threshold
    {
      if abs_real(numbers[i] - numbers[j]) < threshold {
        res := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
