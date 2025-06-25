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

fn Max(a: Vec<nat>) -> (m: int)
    ensures
        a.len() > 0 ==> forall k :: 0<=k<a.len() ==> m >= a.spec_index(k)// not strong enough,
        a.len() == 0 ==> m == -1,
        a.len() > 0 ==> m in a.spec_index(..) // finally at the top // approach did not work for recusrive function
{
    return 0;
}

}