

// <vc-helpers>

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
  var c : set<int> := {};
  var i : int := 0;
  while i < |l1| {
    if l1[i] in l2 {
      c := c + {l1[i]};
    }
    i := i + 1;
  }
  return c;
}
// </vc-code>

