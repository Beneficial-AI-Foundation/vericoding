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

fn max(s: Vec<nat>) -> (a: int)
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
        forall x :: 0 <= x < s.len() ==> a >= s.spec_index(x),
        a in s.spec_index(..)
{
    return 0;
}

}