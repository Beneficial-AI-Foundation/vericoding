// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_max(s: Vec<nat>) -> a:int)
requires s.Length > 0
ensures forall x :: 0 <= x < s.Length ==> a >= s[x]
ensures a in s[..]
{
  a := 0;
  assume forall x :: 0 <= x < s.Length ==> a >= s[x];
  assume a in s[..];
  return a;
}


// SPEC

method Checker(
    requires
        s.len() > 0
    ensures
        forall |x: int| 0 <= x < s.len() ==> a >= s.index(x),
        a in s.index(..)
;

proof fn lemma_max(s: Vec<nat>) -> (a: int)
requires s.Length > 0
ensures forall x :: 0 <= x < s.Length ==> a >= s[x]
ensures a in s[..]
{
  a := 0;
  assume forall x :: 0 <= x < s.Length ==> a >= s[x];
  assume a in s[..];
  return a;
}


// SPEC

method Checker()
    requires
        s.len() > 0
    ensures
        forall |x: int| 0 <= x < s.len() ==> a >= s.index(x),
        a in s.index(..)
{
    0
}

}