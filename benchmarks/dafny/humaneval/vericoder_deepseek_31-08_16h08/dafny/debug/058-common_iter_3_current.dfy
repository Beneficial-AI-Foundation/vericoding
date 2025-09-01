

// <vc-helpers>
predicate InSeq<T(==)>(x: T, s: seq<T>) {
  exists i :: 0 <= i < |s| && s[i] == x
}

lemma InSeqMembership<T(==)>(x: T, s: seq<T>)
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
  var s := set i | i in l1 && i in l2;
  c := s;
}
// </vc-code>

