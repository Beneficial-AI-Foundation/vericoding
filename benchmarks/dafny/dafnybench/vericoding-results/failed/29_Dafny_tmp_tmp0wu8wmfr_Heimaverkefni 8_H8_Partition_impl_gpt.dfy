// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/GW7a

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://www.rise4fun.com/Dafny/JPGct

// Klárið að forrita föllin tvö.

// <vc-helpers>
// no helpers needed
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
  p :| p in m;
  pre := multiset t: (int, int)
           | 1 <= t.1 && t.1 <= m[t.0] && t.0 <= p && !(t.0 == p && t.1 == 1)
           :: t.0;
  post := multiset t: (int, int)
           | 1 <= t.1 && t.1 <= m[t.0] && t.0 > p
           :: t.0;
}
// </vc-code>

