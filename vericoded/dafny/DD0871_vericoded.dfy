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
  result := false;
  
  if |numbers| <= 1 {
    return;
  }
  
  var i := 0;
  while i < |numbers| && !result
    invariant 0 <= i <= |numbers|
    invariant result <==> (exists i', j' ::
      0 <= i' < i &&
      0 <= j' < |numbers| &&
      i' != j' &&
      abs(numbers[i'] - numbers[j']) < threshold)
  {
    var j := 0;
    while j < |numbers| && !result
      invariant 0 <= j <= |numbers|
      invariant result <==> (
        (exists j' :: 0 <= j' < j && i != j' && abs(numbers[i] - numbers[j']) < threshold) || 
        (exists i', j'' :: 0 <= i' < i && 0 <= j'' < |numbers| && i' != j'' && 
          abs(numbers[i'] - numbers[j'']) < threshold))
    {
      if i != j && abs(numbers[i] - numbers[j]) < threshold {
        result := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

