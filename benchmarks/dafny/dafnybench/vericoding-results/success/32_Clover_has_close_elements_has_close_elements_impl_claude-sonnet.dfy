

// <vc-helpers>
function abs(x: real): real
{
  if x >= 0.0 then x else -x
}

lemma abs_properties(x: real, y: real)
  ensures abs(x - y) == abs(y - x)
  ensures abs(x - y) >= 0.0
{
}

lemma abs_definition(x: real, y: real)
  ensures abs(x - y) == (if x - y < 0.0 then y - x else x - y)
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
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant forall p: int, q: int :: 0 <= p < i && 0 <= q < |numbers| && p != q ==> abs(numbers[p] - numbers[q]) >= threshold
  {
    var j := 0;
    while j < |numbers|
      invariant 0 <= j <= |numbers|
      invariant forall q: int :: 0 <= q < j && i != q ==> abs(numbers[i] - numbers[q]) >= threshold
    {
      if i != j {
        abs_definition(numbers[i], numbers[j]);
        var distance := if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j];
        if distance < threshold {
          return true;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

