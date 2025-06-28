// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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