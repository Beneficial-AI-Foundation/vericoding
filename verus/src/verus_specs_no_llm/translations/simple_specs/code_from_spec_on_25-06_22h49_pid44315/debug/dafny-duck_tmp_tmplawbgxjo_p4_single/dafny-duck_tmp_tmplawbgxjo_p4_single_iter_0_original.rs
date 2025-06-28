// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn single(x: Vec<int>, y: Vec<int>) -> (b: Vec<int>)
    requires
        x.len() > 0,
        y.len() > 0
// ensuring that the new array is the two arrays joined
    ensures
        b.spec_index(..) == x.spec_index(..) + y.spec_index(..)
{
    return Vec::new();
}

}