// <vc-helpers>
// Helper predicate to check if there are two distinct elements in the sequence that sum to zero
predicate HasPairSumToZero(s: seq<int>)
{
  exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] + s[j] == 0
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def pairs_sum_to_zero(numbers: List[int]) -> Bool
pairs_sum_to_zero takes a list of integers as an input. it returns True if there are two distinct elements in the list that sum to zero, and False otherwise.
*/
// </vc-description>

// <vc-spec>
method PairsSumToZero(numbers: seq<int>) returns (result: bool)
  ensures result == HasPairSumToZero(numbers)
// </vc-spec>
// <vc-code>
{
  var n := |numbers|;
  if n < 2 {
    return false;
  }
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k, l :: 0 <= k < i && 0 <= l < n && k != l ==> numbers[k] + numbers[l] != 0
  {
    var j := i + 1;
    while j < n
      invariant 0 <= i < j <= n
      invariant forall k, l :: 0 <= k < i && 0 <= l < n && k != l ==> numbers[k] + numbers[l] != 0
      invariant forall l :: i < l < j ==> numbers[i] + numbers[l] != 0
    {
      if numbers[i] + numbers[j] == 0 {
        return true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>
