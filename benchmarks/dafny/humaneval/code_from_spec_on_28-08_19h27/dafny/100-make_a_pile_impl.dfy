// <vc-helpers>
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
  ensures forall i :: 0 <= i < n ==> pile[i] == n + i
  ensures forall i :: 0 <= i < n ==> pile[i] > 0
// </vc-spec>
// <vc-code>
{
  pile := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |pile| == i
    invariant forall j :: 0 <= j < i ==> pile[j] == n + j
  {
    pile := pile + [n + i];
    i := i + 1;
  }
}
// </vc-code>
