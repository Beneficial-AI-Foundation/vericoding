// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn sum(s: Vec<int>) -> (a: int)
    requires s.len() > 0
    ensures sumcheck(s, s.len()) == a
{
}

}