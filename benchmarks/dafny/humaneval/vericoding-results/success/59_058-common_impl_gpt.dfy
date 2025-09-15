// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SetOfCommons(l1: seq<int>, l2: seq<int>): set<int> { set x | x in l1 && x in l2 }
// </vc-helpers>

// <vc-spec>
method common(l1 : seq<int>, l2 : seq<int>) returns (c : set<int>)

    ensures forall i :: i in c ==> i in l1 && i in l2
    ensures forall i :: i in l1 && i in l2 ==> i in c
// </vc-spec>
// <vc-code>
{
  c := SetOfCommons(l1, l2);
}
// </vc-code>
