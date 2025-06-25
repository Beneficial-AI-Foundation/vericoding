// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Total(a: Seq<nat>) -> (r: nat)
    ensures
        r == total (a.spec_index(0..a.len()))
{
    return 0;
}

}