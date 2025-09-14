// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/GW7a

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://www.rise4fun.com/Dafny/JPGct

// Klárið að forrita föllin tvö.

// <vc-helpers>
function SubMultiset(m: multiset<int>, pred: (int -> bool)): multiset<int>
  decreases |m|
{
  if |m| == 0 then multiset{}
  else 
    var x :| x in m && forall y | y in m :: y >= x;
    var rest := m - multiset{x};
    var subm := SubMultiset(rest, pred);
    if pred(x) then subm + multiset{x} else subm
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
  p :| p in m && forall q | q in m :: q >= p;
  var mMinusP := m - multiset{p};
  pre := SubMultiset(mMinusP, y => y < p);
  post := SubMultiset(mMinusP, y => y >= p);
}
// </vc-code>

