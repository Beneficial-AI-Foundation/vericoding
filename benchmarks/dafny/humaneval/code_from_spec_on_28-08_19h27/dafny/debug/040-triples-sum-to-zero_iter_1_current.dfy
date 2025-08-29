// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def triples_sum_to_zero(numbers: List[int]) -> Bool
triples_sum_to_zero takes a list of integers as an input. it returns True if there are three distinct elements in the list that sum to zero, and False otherwise.
*/
// </vc-description>

// <vc-spec>
method triples_sum_to_zero(numbers: seq<int>) returns (result: bool)
  ensures result <==> exists i, j, k :: 0 <= i < j < k < |numbers| && numbers[i] + numbers[j] + numbers[k] == 0
// </vc-spec>
// <vc-code>
{
  result := false;
  var n := |numbers|;
  
  if n < 3 {
    return;
  }
  
  var i := 0;
  while i < n - 2 && !result
    invariant 0 <= i <= n - 2
    invariant result <==> exists i', j', k' :: 0 <= i' < j' < k' < i && numbers[i'] + numbers[j'] + numbers[k'] == 0
  {
    var j := i + 1;
    while j < n - 1 && !result
      invariant i + 1 <= j <= n - 1
      invariant result <==> (exists i', j', k' :: 0 <= i' < j' < k' < i && numbers[i'] + numbers[j'] + numbers[k'] == 0) ||
                           (exists k' :: i < k' < j && numbers[i] + numbers[k'] + numbers[j] == 0)
    {
      var k := j + 1;
      while k < n && !result
        invariant j + 1 <= k <= n
        invariant result <==> (exists i', j', k' :: 0 <= i' < j' < k' < i && numbers[i'] + numbers[j'] + numbers[k'] == 0) ||
                             (exists k' :: i < k' < j && numbers[i] + numbers[k'] + numbers[j] == 0) ||
                             (exists k' :: j < k' < k && numbers[i] + numbers[j] + numbers[k'] == 0)
      {
        if numbers[i] + numbers[j] + numbers[k] == 0 {
          result := true;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
