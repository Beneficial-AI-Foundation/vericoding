// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/GW7a

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://www.rise4fun.com/Dafny/JPGct

// Klárið að forrita föllin tvö.

// <vc-helpers>
lemma MultisetSumLemma(m: multiset<int>, p: int)
  requires p in m
  ensures m == multiset(x | x in m.Elements && x < p :: m[x]) + 
             multiset{p} + 
             multiset(x | x in m.Elements && x > p :: m[x])
{
  var m' := m - multiset{p};
  calc {
    m;
    m' + multiset{p};
    { assert m'.Elements == m.Elements - {p}; }
    multiset(x | x in m'.Elements && x < p :: m'[x]) +
    multiset(x | x in m'.Elements && x == p :: m'[x]) +
    multiset(x | x in m'.Elements && x > p :: m'[x]) +
    multiset{p};
    { assert forall x | x in m'.Elements && x == p :: false; }
    multiset(x | x in m'.Elements && x < p :: m'[x]) +
    multiset{} +
    multiset(x | x in m'.Elements && x > p :: m'[x]) +
    multiset{p};
    multiset(x | x in m.Elements && x < p :: m[x]) +
    multiset{p} +
    multiset(x | x in m.Elements && x > p :: m[x]);
  }
}
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
  var p :| p in m;
  var m' := m - multiset{p};
  pre := multiset(x | x in m.Elements && x < p :: m[x]);
  post := multiset(x | x in m.Elements && x > p :: m[x]);
}
// </vc-code>

