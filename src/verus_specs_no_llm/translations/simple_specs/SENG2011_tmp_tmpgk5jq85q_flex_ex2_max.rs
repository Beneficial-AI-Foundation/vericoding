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
    requires
        s.len() > 0
    ensures
        forall x :: 0 <= x < s.len() ==> a >= s.spec_index(x),
        a in s.spec_index(..)
{
    return 0;
}

}