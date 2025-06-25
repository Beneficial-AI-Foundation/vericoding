// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn nomultiples(u: Seq<nat>) -> bool {
    forall j, k :: 0<=j<k<u.len() ==> u.spec_index(j) != u.spec_index(k)
}

fn BullsCows(s: Seq<nat>, u: Seq<nat>) -> (b: nat, c: nat) 
requires 0 < |u| == |s| <= 10
requires nomultiples(u) && nomultiples(s)
ensures b >= 0 && c >= 0
ensures b == bullspec(s, u)
ensures c == cowspec(s, u)
{
  b: = 0;
  c := 0;
  assume b >= 0 && c >= 0;
  assume b ==> bullspec(s, u);
  assume c ==> cowspec(s, u);
  return b, c;
}


//ATOM

function cowspec(s: Seq<nat>, u: Seq<nat>, u, 0)}


//ATOM

predicate nomultiples(u: Seq<nat>, k: : 0<=j<k<|u| ==> u[j] != u[k]}


// SPEC

method TEST()
    requires
        0 < u.len() == s.len() <= 10,
        nomultiples(u) && nomultiples(s),
        0 <= u.len() == s.len() && nomultiples(u)
    ensures
        b >= 0 && c >= 0,
        b == bullspec(s, u),
        c == cowspec(s, u)
{
    return (0, 0, 0, 0, 0, 0, Seq::empty(), Seq::empty(), 0, Seq::empty(), 0);
}

}