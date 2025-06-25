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

fn factIter(n: nat) -> (a: nat)
    requires
        n >= 0
    ensures
        a == fact(n)
{
    return 0;
}

}