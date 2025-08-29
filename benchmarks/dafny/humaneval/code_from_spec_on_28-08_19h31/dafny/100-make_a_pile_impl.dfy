// <vc-helpers>
// No additional helpers needed for this fix
// </vc-helpers>

// <vc-spec>
method make_a_pile(n: int) returns (pile: seq<int>)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures |pile| == n
  ensures forall i :: 1 <= i < n ==> pile[i] == pile[i - 1] + 2
  ensures n > 0 ==> pile[0] == n
  // post-conditions-end
// </vc-spec>
// <vc-code>
method MakeAPile(n: int) returns (pile: seq<int>)
  requires n >= 0
  ensures |pile| == n
  ensures forall i :: 1 <= i < n ==> pile[i] == pile[i - 1] + 2
  ensures n > 0 ==> pile[0] == n
{
  var result: seq<int> := [];
  if n == 0 {
    return result;
  }
  result := result + [n];
  var i := 1;
  while i < n
    invariant |result| == i
    invariant forall j :: 1 <= j < i ==> result[j] == result[j - 1] + 2
    invariant result[0] == n
  {
    result := result + [result[i - 1] + 2];
    i := i + 1;
  }
  pile := result;
  return pile;
}
// </vc-code>
