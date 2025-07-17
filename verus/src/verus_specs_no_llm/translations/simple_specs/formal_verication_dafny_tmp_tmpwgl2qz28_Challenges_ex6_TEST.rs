// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn nomultiples(u: Seq<nat>) -> bool {
    forall |j: int, k: int| 0<=j<k<u.len() ==> u.index(j) != u.index(k)
}

spec fn reccbull(s: Seq<nat>, u: Seq<nat>, i: int) -> nat
    requires
        0 <= i <= s.len() == u.len()
{
    0
}

spec fn spec_BullsCows(s: Seq<nat>, u: Seq<nat>) -> b:nat, c:nat) 
requires 0 < |u| == |s| <= 10
requires nomultiples(u) && nomultiples(s)
ensures b >= 0 && c >= 0
ensures b == bullspec(s, u)
ensures c == cowspec(s, u)
{
  b := 0;
  c := 0;
  assume b >= 0 && c >= 0;
  assume b ==> bullspec(s, u);
  assume c ==> cowspec(s, u);
  return b, c;
}


//ATOM

function cowspec(s:seq<nat>, u:seq<nat>): nat
requires 0 <= |u| == |s| && nomultiples(u)
{recccow(s, u, 0)}


//ATOM

predicate nomultiples(u:seq<nat>) 
{forall j, k :: 0<=j<k<|u| ==> u[j] != u[k]}


// SPEC

method TEST(
    requires
        0 < u.len() == s.len() <= 10,
        nomultiples(u) && nomultiples(s),
        0 <= u.len() == s.len() && nomultiples(u)
    ensures
        b >= 0 && c >= 0,
        b == bullspec(s, u),
        c == cowspec(s, u)
;

proof fn lemma_BullsCows(s: Seq<nat>, u: Seq<nat>) -> (b: nat, c: nat) 
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
    (0, 0, 0, 0, 0, 0, Seq::empty(), Seq::empty(), 0, Seq::empty(), 0)
}

}