// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn max(s: Vec<nat>) -> (a: int)
    requires s.len() > 0
    ensures forall|x: int| 0 <= x < s.len() ==> a >= s[x],
            a in s[..]
{
}

}