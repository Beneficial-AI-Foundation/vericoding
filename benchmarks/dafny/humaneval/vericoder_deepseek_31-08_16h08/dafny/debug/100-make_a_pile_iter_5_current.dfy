

// <vc-helpers>
lemma ComputePile(n: int) returns (pile: seq<int>)
  requires n >= 0
  ensures |pile| == n
  ensures forall i :: 0 <= i < n ==> pile[i] == n + 2*i
  ensures n > 0 ==> pile[0] == n
{
  pile := [];
  var i := 0;
  while i < n
    invariant |pile| == i
    invariant forall j :: 0 <= j < i ==> pile[j] == n + 2*j
  {
    pile := pile + [n + 2*i];
    i := i + 1;
  }
}
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
{
  var i := 0;
  pile := [];
  while i < n
    invariant |pile| == i
    invariant forall j :: 0 <= j < i ==> pile[j] == n + 2*j
  {
    pile := pile + [n + 2*i];
    i := i + 1;
  }
}
// </vc-code>

