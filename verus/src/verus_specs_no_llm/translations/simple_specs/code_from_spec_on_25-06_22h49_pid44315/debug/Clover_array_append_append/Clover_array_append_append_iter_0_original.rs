// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn append(a: Vec<int>, b: int) -> (c: Vec<int>)
    ensures
        a.spec_index(..) + [b] == c.spec_index(..)
{
    return Vec::new();
}

}