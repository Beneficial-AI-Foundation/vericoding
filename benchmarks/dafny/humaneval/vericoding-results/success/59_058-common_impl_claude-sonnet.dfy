// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SeqToSet(s: seq<int>): set<int> { set x | x in s }
// </vc-helpers>

// <vc-spec>
method common(l1 : seq<int>, l2 : seq<int>) returns (c : set<int>)

    ensures forall i :: i in c ==> i in l1 && i in l2
    ensures forall i :: i in l1 && i in l2 ==> i in c
// </vc-spec>
// <vc-code>
{
  var set1 := SeqToSet(l1);
  var set2 := SeqToSet(l2);
  c := set1 * set2;
}
// </vc-code>
