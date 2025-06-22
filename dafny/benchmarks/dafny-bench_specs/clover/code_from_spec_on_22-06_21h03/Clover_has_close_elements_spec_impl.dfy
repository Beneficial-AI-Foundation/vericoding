//IMPL 
method has_close_elements(numbers: seq<real>, threshold: real) returns (res: bool)
  requires threshold >= 0.0
  ensures res ==> exists i: int, j: int :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) < threshold
  ensures !res ==> (forall i: int, j: int :: 1 <= i < |numbers| && 0 <= j < i ==>  (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) >= threshold)
{
  res := false;
  
  /* code modified by LLM (iteration 4): Changed to check all pairs i,j with i != j */
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant !res ==> (forall k: int, l: int :: 0 <= k < i && 0 <= l < |numbers| && k != l ==> (if numbers[k] - numbers[l] < 0.0 then numbers[l] - numbers[k] else numbers[k] - numbers[l]) >= threshold)
    invariant res ==> exists k: int, l: int :: 0 <= k < |numbers| && 0 <= l < |numbers| && k != l && (if numbers[k] - numbers[l] < 0.0 then numbers[l] - numbers[k] else numbers[k] - numbers[l]) < threshold
  {
    var j := 0;
    while j < |numbers|
      invariant 0 <= j <= |numbers|
      invariant 0 <= i < |numbers|
      invariant !res ==> (forall k: int, l: int :: 0 <= k < i && 0 <= l < |numbers| && k != l ==> (if numbers[k] - numbers[l] < 0.0 then numbers[l] - numbers[k] else numbers[k] - numbers[l]) >= threshold)
      invariant !res ==> (forall l: int :: 0 <= l < j && i != l ==> (if numbers[i] - numbers[l] < 0.0 then numbers[l] - numbers[i] else numbers[i] - numbers[l]) >= threshold)
      invariant res ==> exists k: int, l: int :: 0 <= k < |numbers| && 0 <= l < |numbers| && k != l && (if numbers[k] - numbers[l] < 0.0 then numbers[l] - numbers[k] else numbers[k] - numbers[l]) < threshold
    {
      /* code modified by LLM (iteration 4): Skip when i == j */
      if i != j {
        var diff := if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j];
        if diff < threshold {
          res := true;
          return;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 4): Added lemma to connect full coverage to postcondition requirement */
  if !res {
    assert forall k: int, l: int :: 0 <= k < |numbers| && 0 <= l < |numbers| && k != l ==> (if numbers[k] - numbers[l] < 0.0 then numbers[l] - numbers[k] else numbers[k] - numbers[l]) >= threshold;
    
    // The postcondition follows because if all pairs have distance >= threshold,
    // then specifically all pairs (i,j) with 1 <= i < |numbers| and 0 <= j < i also have distance >= threshold
    assert forall i: int, j: int :: 1 <= i < |numbers| && 0 <= j < i ==> (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) >= threshold;
  }
}