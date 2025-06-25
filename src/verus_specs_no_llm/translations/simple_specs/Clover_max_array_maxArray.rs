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

fn maxArray(a: Vec<int>) -> (m: int)
    requires
        a.len() >= 1
    ensures
        forall k :: 0 <= k < a.len() ==> m >= a.spec_index(k),
        exists k :: 0 <= k < a.len() && m == a.spec_index(k)
{
    return 0;
}

}