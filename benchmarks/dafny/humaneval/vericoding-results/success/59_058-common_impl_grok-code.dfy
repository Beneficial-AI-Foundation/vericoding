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
  for i := 0 to |l1|
    invariant forall x :: x in c <==> exists j :: 0 <= j < i && l1[j] == x && x in l2
  {
    if l1[i] in l2 {
      c := c + {l1[i]};
    }
  }
}
// </vc-code>
