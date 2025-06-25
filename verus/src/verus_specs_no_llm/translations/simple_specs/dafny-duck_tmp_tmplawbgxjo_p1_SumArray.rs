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

fn SumArray(xs: Vec<int>) -> (s: int)
    ensures
        s == Sum(xs.spec_index(..))
{
    return 0;
}

}