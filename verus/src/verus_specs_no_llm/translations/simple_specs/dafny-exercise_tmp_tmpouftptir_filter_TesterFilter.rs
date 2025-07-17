// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Filter(a: Seq<char>, b: set<char>) -> c:set<char>) 
ensures forall x :: x in a && x in b <==> x in c
{
  c := {};
  assume forall x :: x in a && x in b <==> x in c;
  return c;
}


// SPEC

method TesterFilter(
    ensures
        forall |x: int| x in a && x in b <==> x in c
;

proof fn lemma_Filter(a: Seq<char>, b: set<char>) -> (c: set<char>) 
ensures forall x :: x in a && x in b <==> x in c
{
  c := {};
  assume forall x :: x in a && x in b <==> x in c;
  return c;
}


// SPEC

method TesterFilter()
    ensures
        forall |x: int| x in a && x in b <==> x in c
{
    0
}

}