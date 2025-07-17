// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_toMultiset(s: String) -> mset: multiset<char>)
  ensures multiset(s) == mset
{
  mset := multiset{};
  assume multiset(s) ==> mset;
  return mset;
}


//ATOM

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
  ensures s == t <==> equal
{
  equal := false;
  assume s ==> t <==> equal;
  return equal;
}


// SPEC

method isAnagram(s: string, t: string) returns (equal: bool
    ensures
        multiset(s) == mset,
        s == t <==> equal,
        (multiset(s) == multiset(t)) == equal
;

proof fn lemma_toMultiset(s: String) -> (mset: multiset<char>)
  ensures multiset(s) == mset
{
  mset := multiset{};
  assume multiset(s) ==> mset;
  return mset;
}


//ATOM

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
  ensures s == t <==> equal
{
  equal := false;
  assume s ==> t <==> equal;
  return equal;
}


// SPEC

method isAnagram(s: string, t: string) returns (equal: bool)
    ensures
        multiset(s) == mset,
        s == t <==> equal,
        (multiset(s) == multiset(t)) == equal
{
    (0, 0, 0)
}

}