

// <vc-helpers>
lemma ComputePile(n: int) returns (pile: seq<int>)
  requires n >= 0
  ensures |pile| == n
  ensures forall i :: 1 <= i < n ==> pile[i] == pile[i - 1] + 2
  ensures n > 0 ==> pile[0] == n
{
  if n == 0 {
    pile := [];
  } else {
    var p := ComputePile(n - 1);
    pile := [n] + [p[i] + 2 | i in 0..|p|];
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
  if n == 0 {
    pile := [];
  } else {
    pile := ComputePile(n);
  }
}
// </vc-code>

