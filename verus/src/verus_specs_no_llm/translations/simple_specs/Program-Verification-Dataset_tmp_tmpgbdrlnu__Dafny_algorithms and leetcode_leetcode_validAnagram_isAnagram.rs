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

fn toMultiset(s: String) -> (mset: multiset<char>)
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
    return (0, 0, 0);
}

}