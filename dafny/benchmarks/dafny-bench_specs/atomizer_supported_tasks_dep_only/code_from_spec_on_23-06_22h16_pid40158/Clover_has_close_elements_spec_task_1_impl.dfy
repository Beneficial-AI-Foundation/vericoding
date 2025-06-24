//IMPL 
method has_close_elements(numbers: seq<real>, threshold: real) returns (res: bool)
  requires threshold >= 0.0
  ensures res ==> exists i: int, j: int :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) < threshold
  ensures !res ==> (forall i: int, j: int :: 1 <= i < |numbers| && 0 <= j < i ==>  (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) >= threshold)
{
  res := false;
  
  var i := 1;
  while i < |numbers|
    /* code modified by LLM (iteration 3): simplified invariants to focus on the exact postcondition structure */
    invariant 1 <= i <= |numbers|
    invariant !res ==> (forall x: int, y: int :: 1 <= x < i && 0 <= y < x ==> (if numbers[x] - numbers[y] < 0.0 then numbers[y] - numbers[x] else numbers[x] - numbers[y]) >= threshold)
    invariant res ==> exists x: int, y: int :: 0 <= x < |numbers| && 0 <= y < |numbers| && x != y && (if numbers[x] - numbers[y] < 0.0 then numbers[y] - numbers[x] else numbers[x] - numbers[y]) < threshold
  {
    var j := 0;
    while j < i
      /* code modified by LLM (iteration 3): streamlined inner invariants */
      invariant 0 <= j <= i
      invariant !res ==> (forall y: int :: 0 <= y < j ==> (if numbers[i] - numbers[y] < 0.0 then numbers[y] - numbers[i] else numbers[i] - numbers[y]) >= threshold)
      invariant !res ==> (forall x: int, y: int :: 1 <= x < i && 0 <= y < x ==> (if numbers[x] - numbers[y] < 0.0 then numbers[y] - numbers[x] else numbers[x] - numbers[y]) >= threshold)
      invariant res ==> exists x: int, y: int :: 0 <= x < |numbers| && 0 <= y < |numbers| && x != y && (if numbers[x] - numbers[y] < 0.0 then numbers[y] - numbers[x] else numbers[x] - numbers[y]) < threshold
    {
      var dist := if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j];
      if dist < threshold {
        /* code modified by LLM (iteration 3): clear witness establishment */
        assert 0 <= i < |numbers| && 0 <= j < |numbers| && i != j;
        res := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}