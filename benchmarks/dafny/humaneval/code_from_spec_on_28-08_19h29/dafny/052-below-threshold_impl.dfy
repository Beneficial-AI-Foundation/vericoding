// <vc-helpers>
// No additional helpers needed for this specification and implementation
// </vc-helpers>

// <vc-description>
/*
function_signature: def below_threshold(numbers: List[Int], threshold: Int) -> bool
*/
// </vc-description>

// <vc-spec>
method below_threshold(numbers: seq<int>, threshold: int) returns (result: bool)
  ensures result == forall i :: 0 <= i < |numbers| ==> numbers[i] < threshold
// </vc-spec>
// <vc-code>
{
  result := true;
  for i := 0 to |numbers|
    invariant result == forall k :: 0 <= k < i ==> numbers[k] < threshold
  {
    if numbers[i] >= threshold {
      result := false;
      break;
    }
  }
}
// </vc-code>
