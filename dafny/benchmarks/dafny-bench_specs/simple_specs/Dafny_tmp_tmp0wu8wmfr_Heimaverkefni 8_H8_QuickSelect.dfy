// SPEC

  





method QuickSelect( m: multiset<int>, k: int )
    returns( pre: multiset<int>, kth: int, post: multiset<int> )
  requires 0 <= k < |m|
  ensures kth in m
  ensures m == pre+multiset{
}
  ensures |pre| == k
  ensures forall z | z in pre :: z <= kth
  ensures forall z | z in post :: z >= kth
{
}
