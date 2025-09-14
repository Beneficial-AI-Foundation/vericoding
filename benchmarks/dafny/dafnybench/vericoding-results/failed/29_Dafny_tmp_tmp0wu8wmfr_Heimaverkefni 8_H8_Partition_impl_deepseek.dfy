// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/GW7a

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://www.rise4fun.com/Dafny/JPGct

// Klárið að forrita föllin tvö.

// <vc-helpers>
lemma MultisetSplit<T>(m: multiset<T>, x: T)
  requires x in m
  ensures m == (m - multiset{x}) + multiset{x}
{
}

lemma MultisetRemoveAdd<T>(m: multiset<T>, x: T)
  requires x in m
  ensures m == multiset{x} + (m - multiset{x})
{
}

lemma MultisetSubsetProperties<T>(m: multiset<T>, x: T)
  requires x in m
  ensures m - multiset{x} <= m
{
}

lemma MultisetOrdering<T>(m: multiset<T>, x: T, y: T)
  requires x in m && y in m - multiset{x}
  ensures y in m
{
}

lemma MultisetUnion<T>(m1: multiset<T>, m2: multiset<T>, x: T)
  requires x in m1
  ensures x in m1 + m2
{
}

lemma MultisetDistributive<T>(m1: multiset<T>, m2: multiset<T>, m3: multiset<T>)
  ensures m1 + m2 + m3 == m1 + (m2 + m3)
{
}

lemma MultisetAssociative<T>(m1: multiset<T>, m2: multiset<T>, m3: multiset<T>)
  ensures m1 + m2 + m3 == (m1 + m2) + m3
{
}

lemma MultisetSubtractionLemma<T>(m: multiset<T>, x: T)
  requires x in m
  ensures m == multiset{x} + (m - multiset{x})
{
}

lemma MultisetPreservation<T>(m: multiset<T>, x: T)
  ensures x in m ==> (m - multiset{x}) + multiset{x} == m
{
}
// </vc-helpers>
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
  var p_val :| p_val in m;
  p := p_val;
  
  var remaining := m - multiset{p};
  var pre_local := multiset{};
  var post_local := multiset{};
  
  while |remaining| > 0
    invariant remaining + pre_local + post_local + multiset{p} == m
    invariant forall z | z in pre_local :: z <= p
    invariant forall z | z in post_local :: z >= p
    invariant pre_local + post_local + multiset{p} <= m
  {
    var x :| x in remaining;
    if x <= p {
      pre_local := pre_local + multiset{x};
    } else {
      post_local := post_local + multiset{x};
    }
    remaining := remaining - multiset{x};
  }
  
  pre := pre_local;
  post := post_local;
}
// </vc-code>

