

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
  var s := {};
  for i := 0 to |l1| - 1
    invariant 0 <= i <= |l1|
    invariant forall x :: x in s ==> x in l1[..i]
    invariant forall x :: x in s && x in l2 ==> x in l1[..i] && x in l2
  {
    if l2 entails l1[i]
    {
      s := s + {l1[i]};
    }
  }
  return s;
}
// </vc-code>

