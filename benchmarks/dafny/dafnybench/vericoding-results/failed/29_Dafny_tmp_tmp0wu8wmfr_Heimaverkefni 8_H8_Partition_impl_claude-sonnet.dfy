// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/GW7a

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://www.rise4fun.com/Dafny/JPGct

// Klárið að forrita föllin tvö.

// <vc-helpers>

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
    var s := m;
    p :| p in s;
    pre := multiset{};
    post := multiset{};
    s := s - multiset{p};
    
    while s != multiset{}
        invariant p in m
        invariant m == pre + multiset{p} + post + s
        invariant forall z | z in pre :: z <= p
        invariant forall z | z in post :: z >= p
    {
        var x :| x in s;
        s := s - multiset{x};
        if x <= p {
            pre := pre + multiset{x};
        } else {
            post := post + multiset{x};
        }
    }
}
// </vc-code>

