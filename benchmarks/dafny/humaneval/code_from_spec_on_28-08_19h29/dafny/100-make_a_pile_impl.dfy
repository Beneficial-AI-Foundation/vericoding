// <vc-helpers>
// No additional helpers needed for this problem
// </vc-helpers>

// <vc-description>
/*
function_signature: def make_a_pile(n: int) -> List[int]
Given a positive integer n, you have to make a pile of n levels of stones. The first level has n stones. The number of stones in the next level is: Return the number of stones in each level in a list, where element at index i represents the number of stones in the level (i+1).
*/
// </vc-description>

// <vc-spec>
method make_a_pile(n: int) returns (pile: seq<int>)
  requires n > 0
  ensures |pile| == n
  ensures forall i :: 0 <= i < n ==> pile[i] == n - i
// </vc-spec>
// <vc-code>
{
  var result: seq<int> := [];
  for i := 0 to n
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == n - k
  {
    result := result + [n - i];
  }
  return result;
}
// </vc-code>
