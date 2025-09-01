

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
    pile := [n] + [p[i] + 2 | i := 0 to |p|];
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
    var i := 0;
    pile := [n];
    while i < n - 1
      invariant |pile| == i + 1
      invariant i >= 0
      invariant forall j :: 1 <= j <= i ==> pile[j] == pile[j - 1] + 2
    {
      pile := pile + [pile[i] + 2];
      i := i + 1;
    }
  }
}
// </vc-code>

