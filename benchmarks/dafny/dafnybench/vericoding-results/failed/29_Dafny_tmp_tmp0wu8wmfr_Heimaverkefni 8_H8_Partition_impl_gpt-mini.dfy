// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/GW7a

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://www.rise4fun.com/Dafny/JPGct

// Klárið að forrita föllin tvö.

// <vc-helpers>
// No auxiliary helpers required.
// </vc-helpers>

// <vc-spec>
method Partition( m: multiset<int> )
        returns( pre: multiset<int>, p: int, post: multiset<int> )
    requires |m| > 0;
    ensures p in m;
    ensures m == pre+multiset{p}+post;
     ensures forall z | z in pre :: z <= p;
     ensures forall z | z in post :: z >= p;
// </vc-spec>
// <vc-code>
{
  p :| p in m
  pre := multiset{}
  post := multiset{}
  var rest := m - multiset{p}
  while |rest| > 0
    invariant m == pre + post + multiset{p} + rest
    invariant forall z | z in pre :: z <= p
    invariant forall z | z in post :: z >= p
    decreases |rest|
  {
    var x :| x in rest
    rest := rest - multiset{x}
    if x <= p {
      pre := pre + multiset{x}
    } else {
      post := post + multiset{x}
    }
  }
}
// </vc-code>

