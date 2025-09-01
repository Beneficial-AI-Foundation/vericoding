

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method common(l1 : seq<int>, l2 : seq<int>) returns (c : set<int>)
   // post-conditions-start
    ensures forall i :: i in c ==> i in l1 && i in l2
    ensures forall i :: i in l1 && i in l2 ==> i in c
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  c := {};
  var i : int := 0;
  while i < |l1|
    decreases |l1| - i
    invariant 0 <= i <= |l1|
    invariant c == { l1[j] | 0 <= j < i && exists k :: 0 <= k < |l2| && l1[j] == l2[k] }
  {
    if l1[i] in l2 {
      c := c + {l1[i]};
    }
    i := i + 1;
  }
  return c;
}
// </vc-code>

