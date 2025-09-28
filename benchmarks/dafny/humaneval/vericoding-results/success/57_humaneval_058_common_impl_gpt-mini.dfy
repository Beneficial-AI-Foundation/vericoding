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
  var res: set<int> := {};
  var i := 0;
  while i < |l1|
    invariant 0 <= i <= |l1|
    invariant forall x :: x in res <==> x in SeqToSet(l1[..i]) && x in SeqToSet(l2)
  {
    var x := l1[i];
    if x in SeqToSet(l2) {
      res := res + {x};
    }
    i := i + 1;
  }
  c := res;
}
// </vc-code>
