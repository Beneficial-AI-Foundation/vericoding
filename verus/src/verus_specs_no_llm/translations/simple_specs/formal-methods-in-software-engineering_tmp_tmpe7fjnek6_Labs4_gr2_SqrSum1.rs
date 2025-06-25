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

fn SqrSum1(n: int) -> (s: int)
    requires
        n >= 0
    ensures
        s == SqrSumRec(n)
{
    return 0;
}

}