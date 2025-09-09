// SPEC
// Höfundur spurningar: Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/GW7a

// Höfundur lausnar:   Alexander Guðmundsson
// Permalink lausnar:  https://www.rise4fun.com/Dafny/JPGct

// Klárið að forrita föllin tvö.

method Partition( m: multiset<int> )
    returns( pre: multiset<int>, p: int, post: multiset<int> )
  requires |m| > 0
  ensures p in m
  ensures m == pre+multiset{
}
  ensures forall z | z in pre :: z <= p
  ensures forall z | z in post :: z >= p
{
}
