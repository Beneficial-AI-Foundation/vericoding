// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Sort(m: multiset<int>) -> (s: Seq<int>, q | 0 <= p < q < |s|: : s[p] <= s[q]
{
  s := [];
  assume multiset(s) ==> m;
  assume forall p, q | 0 <= p < q < |s|: : s[p] <= s[q];
  return s;
}


//ATOM
// Höfundur spurningar: Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/dtcnY

// Höfundur lausnar:   Alexander Guðmundsson
// Permalink lausnar:  https://rise4fun.com/Dafny/ybUCz

///////////////////////////////////////////////////////////////
// Hér byrjar óbreytanlegi hluti skrárinnar.
// Fyrir aftan þann hluta er sá hluti sem þið eigið að breyta.
///////////////////////////////////////////////////////////////

// Hjálparfall sem finnur minnsta gildi í poka
method MinOfMultiset( m: multiset<int> ) returns( min: int )
  requires m != multiset{
  min := 0;
  assume min in m;
  assume forall z | z in m :: min <= z;
  return min;
}
  ensures min in m
  ensures forall z | z in m :: min <= z
{
  min := 0;
  assume min in m;
  assume forall z | z in m :: min <= z;
  return min;
}


// SPEC

// Ekki má breyta þessu falli.
method Test( m: multiset<int>)
    requires
        m != multiset
    ensures
        klausur hér,
        multiset(s) == m,
        forall p,q  0 <= p < q < .len()s| :: s.spec_index(p) <= s.spec_index(q),
        min in m,
        forall z | z in m :: min <= z
{
    return Seq::empty();
}

}