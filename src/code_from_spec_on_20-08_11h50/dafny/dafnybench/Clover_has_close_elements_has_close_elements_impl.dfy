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
  
  var i := 1;
  while i < |numbers|
    invariant 1 <= i <= |numbers|
    invariant forall ii: int, jj: int :: 1 <= ii < i && 0 <= jj < ii ==> (if numbers[ii] - numbers[jj] < 0.0 then numbers[jj] - numbers[ii] else numbers[ii] - numbers[jj]) >= threshold
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant forall jj: int :: 0 <= jj < j ==> (if numbers[i] - numbers[jj] < 0.0 then numbers[jj] - numbers[i] else numbers[i] - numbers[jj]) >= threshold
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