

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
  res := false;
  
  for i := 0 to |numbers|
    invariant 0 <= i <= |numbers|
    invariant !res ==> (forall i': int, j': int :: 0 <= i' < i && 0 <= j' < |numbers| && i' != j' ==> 
                         (if numbers[i'] - numbers[j'] < 0.0 then numbers[j'] - numbers[i'] else numbers[i'] - numbers[j']) >= threshold)
  {
    for j := 0 to |numbers|
      invariant 0 <= j <= |numbers|
      invariant !res ==> (forall j': int :: 0 <= j' < j && i != j' ==> 
                           (if numbers[i] - numbers[j'] < 0.0 then numbers[j'] - numbers[i] else numbers[i] - numbers[j']) >= threshold)
      invariant !res ==> (forall i': int, j': int :: 0 <= i' < i && 0 <= j' < |numbers| && i' != j' ==> 
                           (if numbers[i'] - numbers[j'] < 0.0 then numbers[j'] - numbers[i'] else numbers[i'] - numbers[j']) >= threshold)
    {
      if i != j {
        var diff := if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j];
        if diff < threshold {
          res := true;
          return;
        }
      }
    }
  }
}
// </vc-code>

