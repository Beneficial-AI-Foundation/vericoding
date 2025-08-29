// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def below_threshold(numbers: List[Int], threshold: Int) -> bool
*/
// </vc-description>

// <vc-spec>
method below_threshold(numbers: seq<int>, threshold: int) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |numbers| ==> numbers[i] < threshold
// </vc-spec>
// <vc-code>
method below_threshold(numbers: seq<int>, threshold: int) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |numbers| ==> numbers[i] < threshold
{
  if |numbers| == 0 {
    return true;
  }
  
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant forall j :: 0 <= j < i ==> numbers[j] < threshold
  {
    if numbers[i] >= threshold {
      return false;
    }
    i := i + 1;
  }
  
  return true;
}
// </vc-code>
