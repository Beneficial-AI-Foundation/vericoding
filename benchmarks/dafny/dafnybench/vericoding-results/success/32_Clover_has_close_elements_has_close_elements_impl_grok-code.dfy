

// <vc-helpers>
function absreal(a: real, b: real): real {
  if a - b < 0.0 then b - a else a - b
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
  res := false;
  for i : int := 0 to |numbers|
    invariant forall x, y :: 0 <= x < i && 0 <= y < |numbers| && x < y ==> absreal(numbers[x], numbers[y]) >= threshold
  {
    for j : int := i + 1 to |numbers|
      invariant forall z :: i + 1 <= z < j ==> absreal(numbers[i], numbers[z]) >= threshold
    {
      var diff := absreal(numbers[i], numbers[j]);
      if diff < threshold {
        res := true;
        return res;
      }
    }
  }
  return res;
}
// </vc-code>

