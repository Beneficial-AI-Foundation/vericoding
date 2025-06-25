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

fn Total(a: Seq<nat>) -> (r: nat)
    ensures
        r == total (a.spec_index(0..a.len()));
{
    return 0;
}

}