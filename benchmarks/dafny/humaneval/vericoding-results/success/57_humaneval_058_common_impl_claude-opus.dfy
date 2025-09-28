// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method common(l1 : seq<int>, l2 : seq<int>) returns (c : set<int>)

    ensures forall i :: i in c ==> i in l1 && i in l2
    ensures forall i :: i in l1 && i in l2 ==> i in c
// </vc-spec>
// <vc-code>
{
  c := {};
  var i := 0;
  while i < |l1|
    invariant 0 <= i <= |l1|
    invariant forall x :: x in c ==> x in l1[..i] && x in l2
    invariant forall x :: x in l1[..i] && x in l2 ==> x in c
  {
    if l1[i] in l2 {
      c := c + {l1[i]};
    }
    i := i + 1;
  }
}
// </vc-code>
