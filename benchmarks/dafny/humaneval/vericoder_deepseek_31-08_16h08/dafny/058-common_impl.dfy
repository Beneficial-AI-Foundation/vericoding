

// <vc-helpers>
predicate InSeq<T(==)>(x: T, s: seq<T>) {
  exists i :: 0 <= i < |s| && s[i] == x
}

lemma InSeqMembership<T>(x: T, s: seq<T>)
  ensures InSeq(x, s) == (x in s)
{
}
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
  var s: set<int> := {};
  var i: int := 0;
  while i < |l1|
    invariant 0 <= i <= |l1|
    invariant forall x :: x in s ==> x in l1 && x in l2
    invariant forall x :: x in l1[0..i] && x in l2 ==> x in s
  {
    if l1[i] in l2 {
      s := s + {l1[i]};
    }
    i := i + 1;
  }
  c := s;
}
// </vc-code>

