// <vc-helpers>
// Helper predicate to check if three distinct indices in a sequence sum to zero
predicate HasTripleSumToZero(s: seq<int>)
{
  exists i, j, k :: 0 <= i < |s| && 0 <= j < |s| && 0 <= k < |s| && 
                    i != j && i != k && j != k && 
                    s[i] + s[j] + s[k] == 0
}

// Helper predicate to check if a triple summing to zero exists up to a certain index
predicate NoTripleSumToZeroUpTo(s: seq<int>, iLimit: int, jLimit: int, kLimit: int)
{
  forall i, j, k :: 0 <= i < iLimit && 0 <= j < jLimit && 0 <= k < kLimit && 
                    i != j && i != k && j != k ==> 
                    s[i] + s[j] + s[k] != 0
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def triples_sum_to_zero(numbers: List[int]) -> Bool
triples_sum_to_zero takes a list of integers as an input. it returns True if there are three distinct elements in the list that sum to zero, and False otherwise.
*/
// </vc-description>

// <vc-spec>
method TriplesSumToZero(numbers: seq<int>) returns (result: bool)
  ensures result == HasTripleSumToZero(numbers)
// </vc-spec>
// <vc-code>
{
  var n := |numbers|;
  if n < 3 {
    return false;
  }
  
  for i := 0 to n
    invariant 0 <= i <= n
    invariant forall a, b, c :: 0 <= a < i && 0 <= b < n && 0 <= c < n && a != b && a != c && b != c ==> 
                numbers[a] + numbers[b] + numbers[c] != 0
  {
    for j := i+1 to n
      invariant 0 <= i < n
      invariant i+1 <= j <= n
      invariant forall a, b, c :: 0 <= a < i && 0 <= b < n && 0 <= c < n && a != b && a != c && b != c ==> 
                  numbers[a] + numbers[b] + numbers[c] != 0
      invariant forall a, b, c :: a == i && 0 <= b < j && 0 <= c < n && a != b && a != c && b != c ==> 
                  numbers[a] + numbers[b] + numbers[c] != 0
    {
      for k := j+1 to n
        invariant 0 <= i < n
        invariant i+1 <= j < n
        invariant j+1 <= k <= n
        invariant forall a, b, c :: 0 <= a < i && 0 <= b < n && 0 <= c < n && a != b && a != c && b != c ==> 
                    numbers[a] + numbers[b] + numbers[c] != 0
        invariant forall a, b, c :: a == i && 0 <= b < j && 0 <= c < n && a != b && a != c && b != c ==> 
                    numbers[a] + numbers[b] + numbers[c] != 0
        invariant forall a, b, c :: a == i && b == j && 0 <= c < k && a != b && a != c && b != c ==> 
                    numbers[a] + numbers[b] + numbers[c] != 0
      {
        if k < n && numbers[i] + numbers[j] + numbers[k] == 0 {
          return true;
        }
      }
    }
  }
  return false;
}
// </vc-code>
